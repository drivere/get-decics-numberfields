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
#include <pthread.h>

struct mt_queue
{
  long no;
  GEN input, output;
  GEN worker;
  long workid;
  pthread_cond_t cond, cond1, cond2;
  pthread_mutex_t mut, mut1, mut2;
  pthread_cond_t *pcond;
  pthread_mutex_t *pmut;
};

struct mt_pstate
{
  pthread_t *th;
  struct pari_thread *pth;
  struct mt_queue *mq;
  long n, nbint, last;
  long pending;
  pthread_cond_t pcond;
  pthread_mutex_t pmut;
};

static THREAD long mt_thread_no = -1;
static struct mt_pstate *pari_mt;

#define LOCK(x) pthread_mutex_lock(x); do
#define UNLOCK(x) while(0); pthread_mutex_unlock(x)

void
mt_sigint_block(void)
{
  if (mt_thread_no>=0)
    pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED,NULL);
}

void
mt_sigint_unblock(void)
{
  if (mt_thread_no>=0)
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS,NULL);
}

void
mt_err_recover(long er)
{
  (void) er;
  if (mt_thread_no>=0)
  {
    struct mt_pstate *mt = pari_mt;
    struct mt_queue *mq = mt->mq+mt_thread_no;
    LOCK(mq->pmut)
    {
      mq->output = pari_err_last();
      pthread_cond_signal(mq->pcond);
    } UNLOCK(mq->pmut);
    pthread_exit((void*)1);
  }
}

void
mt_sigint(void)
{
  if (pari_mt) pthread_cond_broadcast(&pari_mt->pcond);
}

int
mt_is_parallel(void)
{
  return !!pari_mt;
}

int
mt_is_thread(void)
{
  return mt_thread_no>=0;
}

void mt_broadcast(GEN code) {(void) code;}

void pari_mt_init(void)
{
  pari_mt = NULL;
#ifdef _SC_NPROCESSORS_CONF
  pari_mt_nbthreads = sysconf(_SC_NPROCESSORS_CONF);
#else
  pari_mt_nbthreads = 1;
#endif
}

void pari_mt_close(void) { }

static void*
mt_queue_run(void *arg)
{
  GEN args = pari_thread_start((struct pari_thread*) arg);
  pari_sp av = avma;
  struct mt_queue *mq = (struct mt_queue *) args;
  mt_thread_no = mq->no;
  for(;;)
  {
    GEN work, done;
    LOCK(&mq->mut)
    {
      while(!mq->input)
        pthread_cond_wait(&mq->cond, &mq->mut);
    } UNLOCK(&mq->mut);
    work = gcopy(mq->input);
    LOCK(&mq->mut1)
    {
      mq->input = NULL;
      pthread_cond_signal(&mq->cond1);
    } UNLOCK(&mq->mut1);
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS,NULL);
    done = closure_callgenvec(mq->worker,work);
    pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED,NULL);
    LOCK(mq->pmut)
    {
      mq->output = done;
      pthread_cond_signal(mq->pcond);
    } UNLOCK(mq->pmut);
    LOCK(&mq->mut2)
    {
      while(mq->output)
        pthread_cond_wait(&mq->cond2, &mq->mut2);
    } UNLOCK(&mq->mut2);
    avma = av;
  }
  return NULL;
}

static long
mt_queue_check(struct mt_pstate *mt)
{
  long i;
  for(i=0; i<mt->n; i++)
  {
    struct mt_queue *mq = mt->mq+i;
    if (mq->output) return i;
  }
  return -1;
}

static GEN
mtpthread_queue_get(struct mt_state *junk, long *workid, long *pending)
{
  struct mt_pstate *mt = pari_mt;
  struct mt_queue *mq;
  GEN done = NULL;
  long last;
  (void) junk;
  if (mt->nbint<mt->n) { mt->last = mt->nbint; *pending = mt->pending; return NULL; }
  BLOCK_SIGINT_START
  LOCK(&mt->pmut)
  {
    while ((last = mt_queue_check(mt)) < 0)
    {
      pthread_cond_wait(&mt->pcond, &mt->pmut);
      if (PARI_SIGINT_pending)
      {
        int sig = PARI_SIGINT_pending;
        PARI_SIGINT_pending = 0;
        pthread_mutex_unlock(&mt->pmut);
        PARI_SIGINT_block = 0;
        raise(sig);
        PARI_SIGINT_block = 1;
        pthread_mutex_lock(&mt->pmut);
      }
    }
  } UNLOCK(&mt->pmut);
  BLOCK_SIGINT_END
  mq = mt->mq+last;
  if (mq->output==err_e_STACK) pari_err(e_STACK);
  done = gcopy(mq->output);
  if (workid) *workid = mq->workid;
  if (typ(done)==t_ERROR) pari_err(0,done);
  BLOCK_SIGINT_START
  LOCK(&mq->mut2)
  {
    mq->output = NULL;
    pthread_cond_signal(&mq->cond2);
  } UNLOCK(&mq->mut2);
  mt->last = last;
  mt->pending--;
  BLOCK_SIGINT_END
  *pending = mt->pending;
  return done;
}

static void
mtpthread_queue_submit(struct mt_state *junk, long workid, GEN work)
{
  struct mt_pstate *mt = pari_mt;
  struct mt_queue *mq = mt->mq+mt->last;
  (void) junk;
  if (!work) { mt->nbint=mt->n; return; }
  BLOCK_SIGINT_START
  if (mt->nbint<mt->n) mt->nbint++;
  LOCK(&mq->mut)
  {
    mq->input = work;
    mq->workid = workid;
    pthread_cond_signal(&mq->cond);
  } UNLOCK(&mq->mut);
  mt->pending++;
  LOCK(&mq->mut1)
  {
    while (mq->input)
      pthread_cond_wait(&mq->cond1, &mq->mut1);
  } UNLOCK(&mq->mut1);
  BLOCK_SIGINT_END
}

void
mt_queue_reset(void)
{
  struct mt_pstate *mt = pari_mt;
  long i;
  for (i=0; i<mt->n; i++)
    pthread_cancel(mt->th[i]);
  for (i=0; i<mt->n; i++)
    pthread_join(mt->th[i],NULL);
  if (DEBUGLEVEL) pari_warn(warner,"stop threads");
  pari_mt = NULL;
  for (i=0;i<mt->n;i++)
  {
    struct mt_queue *mq = mt->mq+i;
    pthread_cond_destroy(&mq->cond);
    pthread_cond_destroy(&mq->cond1);
    pthread_cond_destroy(&mq->cond2);
    pthread_mutex_destroy(&mq->mut);
    pthread_mutex_destroy(&mq->mut1);
    pthread_mutex_destroy(&mq->mut2);
    pari_thread_free(&mt->pth[i]);
  }
  pari_free(mt->mq);
  pari_free(mt->pth);
  pari_free(mt->th);
  pari_free(mt);
}

void
mt_queue_start(struct pari_mt *pt, GEN worker)
{
  if (pari_mt)
    return mtsingle_queue_start(pt, worker);
  else
  {
    long NBT = pari_mt_nbthreads;
    struct mt_pstate *mt =
           (struct mt_pstate*) pari_malloc(sizeof(struct mt_pstate));
    long mtparisize = GP_DATA->threadsize? GP_DATA->threadsize: top-bot;
    long i;
    mt->mq  = (struct mt_queue *) pari_malloc(sizeof(*mt->mq)*NBT);
    mt->th  = (pthread_t *) pari_malloc(sizeof(*mt->th)*NBT);
    mt->pth = (struct pari_thread *) pari_malloc(sizeof(*mt->pth)*NBT);
    mt->pending = 0;
    mt->n = NBT;
    mt->nbint = 0;
    mt->last = 0;
    pari_mt = mt;
    pthread_cond_init(&mt->pcond,NULL);
    pthread_mutex_init(&mt->pmut,NULL);
    for (i=0;i<NBT;i++)
    {
      struct mt_queue *mq = mt->mq+i;
      mq->no     = i;
      mq->worker = worker;
      mq->input  = NULL;
      mq->output = NULL;
      mq->pcond  = &mt->pcond;
      mq->pmut   = &mt->pmut;
      pthread_cond_init(&mq->cond,NULL);
      pthread_cond_init(&mq->cond1,NULL);
      pthread_cond_init(&mq->cond2,NULL);
      pthread_mutex_init(&mq->mut,NULL);
      pthread_mutex_init(&mq->mut1,NULL);
      pthread_mutex_init(&mq->mut2,NULL);
      pari_thread_alloc(&mt->pth[i],mtparisize,(GEN)mq);
    }
    if (DEBUGLEVEL) pari_warn(warner,"start threads");
    for (i=0;i<NBT;i++)
      pthread_create(&mt->th[i],NULL, &mt_queue_run, (void*)&mt->pth[i]);
    pt->get=&mtpthread_queue_get;
    pt->submit=&mtpthread_queue_submit;
    pt->end=&mt_queue_reset;
  }
}
