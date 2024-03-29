/* Copyright (C) 2013  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
#include "pari.h"
#include "paripriv.h"
#include "mt.h"
#include <mpi.h>

static THREAD int pari_MPI_size, pari_MPI_rank;
static THREAD long nbreq = 0;

enum PMPI_cmd { PMPI_close, PMPI_worker, PMPI_work, PMPI_parisize,
                PMPI_precreal, PMPI_eval };

struct mt_mstate
{
  long n;
  int source;
  long nbint;
  long *workid;
};

static struct mt_mstate pari_mt_data;
static struct mt_mstate *pari_mt;

static void
send_long(long a, long dest)
{
  MPI_Send(&a, 1, MPI_LONG, dest, 0, MPI_COMM_WORLD);
}

static void
send_request(enum PMPI_cmd ecmd, long dest)
{
  send_long((long)ecmd, dest);
}

static void
send_GEN(GEN elt, int dest)
{
  pari_sp av = avma;
  int size;
  GEN reloc = copybin_unlink(elt);
  GENbin *buf = copy_bin(mkvec2(elt,reloc));
  size = sizeof(GENbin) + buf->len*sizeof(ulong);
  MPI_Send(buf, size, MPI_CHAR, dest, 0, MPI_COMM_WORLD);
  pari_free(buf); avma = av;
}

static void
send_request_GEN(enum PMPI_cmd ecmd, GEN elt, int dest)
{
  send_request(ecmd, dest);
  send_GEN(elt, dest);
}

static void
send_request_long(enum PMPI_cmd ecmd, long elt, int dest)
{
  send_request(ecmd, dest);
  send_long(elt, dest);
}

static long
recvfrom_long(int src)
{
  long a;
  MPI_Recv(&a, 1, MPI_LONG, src, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  return a;
}

static enum PMPI_cmd
recvfrom_request(int src)
{
  return (enum PMPI_cmd) recvfrom_long(src);
}

static GENbin *
recvstatus_buf(int source, MPI_Status *status)
{
  int size;
  GENbin *buf;

  MPI_Get_count(status, MPI_CHAR, &size);
  buf = (GENbin *)pari_malloc(size);
  MPI_Recv(buf, size, MPI_CHAR, source, 0/* tag */,
          MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  return buf;
}

static GEN
recvstatus_GEN(int source, MPI_Status *status)
{
  GENbin *buf = recvstatus_buf(source, status);
  GEN res = bin_copy(buf);
  bincopy_relink(gel(res,1),gel(res,2));
  return gel(res,1);
}

static void
recvstatus_void(int source, MPI_Status *status)
{
  GENbin *buf = recvstatus_buf(source, status);
  free(buf);
}

static GEN
recvfrom_GEN(int src)
{
  MPI_Status status;
  MPI_Probe(src, 0, MPI_COMM_WORLD, &status);
  return recvstatus_GEN(src, &status);
}

static GEN
recvany_GEN(int *source)
{
  MPI_Status status;
  MPI_Probe(MPI_ANY_SOURCE, 0 /* tag */, MPI_COMM_WORLD, &status);
  *source = status.MPI_SOURCE;
  return recvstatus_GEN(*source, &status);
}

static void
recvany_void(int *source)
{
  MPI_Status status;
  MPI_Probe(MPI_ANY_SOURCE, 0 /* tag */, MPI_COMM_WORLD, &status);
  *source = status.MPI_SOURCE;
  recvstatus_void(*source, &status);
}

static jmp_buf child_env;

static void
pari_MPI_child(void)
{
  pari_sp av = avma;
  long size;
  GEN worker = NULL, work, done;
  struct gp_context rec;
  if (!diffptr) initprimetable(500000);
  gp_context_save(&rec);
  if (setjmp(child_env))
  {
    send_GEN(pari_err_last(), 0);
    gp_context_restore(&rec);
  }
  while (1)
    switch (recvfrom_request(0))
    {
    case PMPI_worker:
      avma = top;
      worker = recvfrom_GEN(0);
      av = avma;
      break;
    case PMPI_work:
      work = recvfrom_GEN(0);
      done = closure_callgenvec(worker, work);
      send_GEN(done, 0);
      avma = av;
      break;
    case PMPI_parisize:
      size = recvfrom_long(0);
      pari_init_stack(size,top-bot);
      gp_context_save(&rec);
      break;
    case PMPI_precreal:
      precreal = recvfrom_long(0);
      break;
    case PMPI_eval:
      (void) closure_evalgen(recvfrom_GEN(0));
      avma = av;
      break;
    case PMPI_close:
      MPI_Barrier(MPI_COMM_WORLD);
      MPI_Finalize();
      exit(0);
      break;
    }
}

void
mt_err_recover(long er)
{
  if (pari_MPI_rank) longjmp(child_env,er);
}
void mt_sigint_block(void) { }
void mt_sigint_unblock(void) { }
void mt_sigint(void) {}

int
mt_is_parallel(void)
{
  return !!pari_mt;
}

int
mt_is_thread(void)
{
  return pari_MPI_rank;
}

void
mt_broadcast(GEN code)
{
  long i;
  if (!pari_MPI_rank && !pari_mt)
    for (i=1;i<pari_MPI_size;i++)
      send_request_GEN(PMPI_eval, code, i);
}

void
pari_mt_init(void)
{
  int res = MPI_Init(0, NULL);
  if (res == MPI_SUCCESS)
  {
    MPI_Comm_size(MPI_COMM_WORLD, &pari_MPI_size);
    MPI_Comm_rank(MPI_COMM_WORLD, &pari_MPI_rank);
    if (pari_MPI_rank) pari_MPI_child();
    pari_mt_nbthreads = pari_MPI_size-1;
  }
  else
  {
    pari_MPI_size = 0;
    pari_MPI_rank = 0;
    pari_mt_nbthreads = 1;
  }
  pari_mt = NULL;
}

void
pari_mt_close(void)
{
  long i;
  if (!pari_MPI_rank)
    for (i = 1; i < pari_MPI_size; i++)
      send_request(PMPI_close, i);
  MPI_Barrier(MPI_COMM_WORLD);
  MPI_Finalize();
}

static GEN
mtmpi_queue_get(struct mt_state *junk, long *workid, long *pending)
{
  struct mt_mstate *mt = pari_mt;
  GEN done;
  if (mt->nbint<=mt->n) { mt->source=mt->nbint; *pending = nbreq; return NULL; }
  done = recvany_GEN(&mt->source);
  nbreq--; *pending = nbreq;
  if (workid) *workid = mt->workid[mt->source];
  if (typ(done) == t_ERROR)
    pari_err(0,done);
  return done;
}

static void
mtmpi_queue_submit(struct mt_state *junk, long workid, GEN work)
{
  struct mt_mstate *mt = pari_mt;
  if (!work) { mt->nbint=mt->n+1; return; }
  if (mt->nbint<=mt->n) mt->nbint++;
  nbreq++;
  mt->workid[mt->source] = workid;
  send_request_GEN(PMPI_work, work, mt->source);
}

void
mt_queue_reset(void)
{
  struct mt_mstate *mt = pari_mt;
  if (DEBUGLEVEL>0 && nbreq)
    pari_warn(warner,"%ld discarded threads (MPI)",nbreq);
  for(  ;nbreq>0;  nbreq--) recvany_void(&mt->source);
  pari_free(mt->workid);
  pari_mt = NULL;
}

void
mt_queue_start(struct pari_mt *pt, GEN worker)
{
  if (pari_mt || pari_MPI_size <= 2 || pari_mt_nbthreads <= 1)
    return mtsingle_queue_start(pt, worker);
  else
  {
    struct mt_mstate *mt = &pari_mt_data;
    long i, n = minss(pari_mt_nbthreads, pari_MPI_size-1);
    long mtparisize = GP_DATA->threadsize? GP_DATA->threadsize: top-bot;
    pari_mt = mt;
    mt->workid = (long*) pari_malloc(sizeof(long)*(n+1));
    for (i=1; i <= n; i++)
    {
      send_request_long(PMPI_parisize, mtparisize, i);
      send_request_long(PMPI_precreal, precreal, i);
      send_request_GEN(PMPI_worker, worker, i);
    }
    mt->n = n;
    mt->nbint = 1;
    mt->source = 1;
    pt->get=&mtmpi_queue_get;
    pt->submit=&mtmpi_queue_submit;
    pt->end=&mt_queue_reset;
  }
}
