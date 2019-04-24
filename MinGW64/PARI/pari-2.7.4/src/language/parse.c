/* A Bison parser, made by GNU Bison 2.5.  */

/* Bison implementation for Yacc-like parsers in C
   
      Copyright (C) 1984, 1989-1990, 2000-2011 Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.5"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 1

/* Substitute the variable and function names.  */
#define yyparse         pari_parse
#define yylex           pari_lex
#define yyerror         pari_error
#define yylval          pari_lval
#define yychar          pari_char
#define yydebug         pari_debug
#define yynerrs         pari_nerrs
#define yylloc          pari_lloc

/* Copy the first part of user declarations.  */

/* Line 268 of yacc.c  */
#line 1 "../src/language/parse.y"

/* Copyright (C) 2006  The PARI group.

This file is part of the PARI package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#define YYSIZE_T size_t
#define YYSTYPE union token_value
#define YYLTYPE struct node_loc
#define YYLLOC_DEFAULT(Current, Rhs, N)     \
        ((Current).start  = ((N)?(Rhs)[1].start:(Rhs)[0].end),  \
         (Current).end    = (Rhs)[N].end)
#include "parsec.h"
#define NOARG(x) newnode(Fnoarg,-1,-1,&(x))


/* Line 268 of yacc.c  */
#line 104 "../src/language/parse.c"

/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     KPARROW = 258,
     KARROW = 259,
     KDOTDOT = 260,
     KPE = 261,
     KSE = 262,
     KME = 263,
     KDE = 264,
     KDRE = 265,
     KEUCE = 266,
     KMODE = 267,
     KAND = 268,
     KOR = 269,
     KID = 270,
     KEQ = 271,
     KNE = 272,
     KGE = 273,
     KLE = 274,
     KSRE = 275,
     KSLE = 276,
     KSR = 277,
     KSL = 278,
     KDR = 279,
     KPP = 280,
     KSS = 281,
     KINTEGER = 282,
     KREAL = 283,
     KENTRY = 284,
     KSTRING = 285,
     DEFFUNC = 286,
     SEQ = 287,
     LVAL = 288,
     INT = 289,
     SIGN = 290
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif

#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} YYLTYPE;
# define yyltype YYLTYPE /* obsolescent; will be withdrawn */
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


/* Copy the second part of user declarations.  */


/* Line 343 of yacc.c  */
#line 193 "../src/language/parse.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
	     && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  46
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   638

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  61
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  21
/* YYNRULES -- Number of rules.  */
#define YYNRULES  109
/* YYNRULES -- Number of states.  */
#define YYNSTATES  189

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   290

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    50,     2,    49,     2,    43,    38,    53,
      55,    59,    46,    41,    36,    42,    54,    45,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    56,    35,
      40,    37,    39,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    52,    44,    57,    48,     2,    58,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    60,     2,    51,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      47
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     8,     9,    11,    14,    18,    19,
      21,    25,    28,    34,    38,    40,    43,    45,    48,    51,
      54,    58,    62,    64,    66,    68,    72,    74,    77,    79,
      84,    86,    88,    90,    92,    94,    98,   102,   105,   108,
     112,   116,   120,   124,   128,   132,   136,   140,   144,   147,
     150,   154,   158,   162,   166,   170,   174,   178,   182,   186,
     190,   194,   198,   202,   206,   210,   214,   218,   222,   226,
     229,   232,   236,   239,   242,   245,   248,   250,   254,   258,
     260,   263,   267,   269,   273,   277,   281,   284,   290,   294,
     298,   302,   306,   311,   313,   317,   321,   327,   333,   335,
     338,   339,   344,   346,   350,   355,   359,   366,   372,   376
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      62,     0,    -1,    63,    -1,    63,     1,    -1,    -1,    68,
      -1,    63,    35,    -1,    63,    35,    68,    -1,    -1,    68,
      -1,    68,     5,    68,    -1,    48,    68,    -1,    52,    64,
      36,    64,    57,    -1,    52,    64,    57,    -1,    58,    -1,
      66,    58,    -1,    43,    -1,    43,    27,    -1,    43,    66,
      -1,    43,    49,    -1,    43,    49,    27,    -1,    43,    49,
      66,    -1,    27,    -1,    28,    -1,    54,    -1,    27,    54,
      29,    -1,    30,    -1,    53,    29,    -1,    67,    -1,    68,
      55,    78,    59,    -1,    79,    -1,    69,    -1,    72,    -1,
      75,    -1,    81,    -1,    72,    37,    68,    -1,    69,    37,
      68,    -1,    69,    25,    -1,    69,    26,    -1,    69,     8,
      68,    -1,    69,     9,    68,    -1,    69,    10,    68,    -1,
      69,    11,    68,    -1,    69,    12,    68,    -1,    69,    21,
      68,    -1,    69,    20,    68,    -1,    69,     6,    68,    -1,
      69,     7,    68,    -1,    50,    68,    -1,    49,    68,    -1,
      68,    14,    68,    -1,    68,    13,    68,    -1,    68,    38,
      68,    -1,    68,    15,    68,    -1,    68,    16,    68,    -1,
      68,    17,    68,    -1,    68,    18,    68,    -1,    68,    39,
      68,    -1,    68,    19,    68,    -1,    68,    40,    68,    -1,
      68,    42,    68,    -1,    68,    41,    68,    -1,    68,    23,
      68,    -1,    68,    22,    68,    -1,    68,    43,    68,    -1,
      68,    24,    68,    -1,    68,    44,    68,    -1,    68,    45,
      68,    -1,    68,    46,    68,    -1,    41,    68,    -1,    42,
      68,    -1,    68,    48,    68,    -1,    68,    51,    -1,    68,
      53,    -1,    68,    50,    -1,    68,    65,    -1,    80,    -1,
      68,    56,    29,    -1,    55,    68,    59,    -1,    29,    -1,
      69,    65,    -1,    69,    56,    29,    -1,    68,    -1,    70,
      36,    68,    -1,    70,    35,    70,    -1,    71,    35,    70,
      -1,    52,    57,    -1,    52,    68,     5,    68,    57,    -1,
      52,    35,    57,    -1,    52,    70,    57,    -1,    52,    71,
      57,    -1,    52,     1,    57,    -1,    69,    40,    42,    68,
      -1,    73,    -1,    73,    36,    68,    -1,    73,    35,    74,
      -1,    73,    36,    68,    35,    74,    -1,    52,    68,    60,
      74,    57,    -1,    63,    -1,    38,    69,    -1,    -1,    76,
       1,    77,    68,    -1,    76,    -1,    78,    36,    76,    -1,
      29,    55,    78,    59,    -1,    68,    54,    29,    -1,    29,
      55,    78,    59,    37,    63,    -1,    68,    54,    29,    37,
      63,    -1,    69,     4,    63,    -1,    55,    78,     3,    63,
      -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] =
{
       0,    85,    85,    86,    89,    90,    91,    92,    95,    96,
      97,    98,   101,   102,   105,   106,   109,   110,   111,   112,
     113,   114,   117,   118,   119,   120,   122,   123,   124,   125,
     126,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,   139,   140,   141,   142,   143,   144,   145,
     146,   147,   148,   149,   150,   151,   152,   153,   154,   155,
     156,   157,   158,   159,   160,   161,   162,   163,   164,   165,
     166,   167,   168,   169,   170,   171,   172,   173,   174,   177,
     178,   179,   182,   183,   186,   187,   190,   191,   192,   193,
     194,   195,   198,   201,   202,   203,   204,   207,   210,   211,
     212,   212,   216,   217,   220,   223,   226,   228,   230,   231
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "\")->\"", "\"->\"", "\"..\"", "\"+=\"",
  "\"-=\"", "\"*=\"", "\"/=\"", "\"\\\\/=\"", "\"\\\\=\"", "\"%=\"",
  "\"&&\"", "\"||\"", "\"===\"", "\"==\"", "\"!=\"", "\">=\"", "\"<=\"",
  "\">>=\"", "\"<<=\"", "\">>\"", "\"<<\"", "\"\\\\/\"", "\"++\"",
  "\"--\"", "\"integer\"", "\"real number\"", "\"variable name\"",
  "\"character string\"", "DEFFUNC", "SEQ", "LVAL", "INT", "';'", "','",
  "'='", "'&'", "'>'", "'<'", "'+'", "'-'", "'%'", "'\\\\'", "'/'", "'*'",
  "SIGN", "'^'", "'#'", "'!'", "'~'", "'['", "'\\''", "'.'", "'('", "':'",
  "']'", "'`'", "')'", "'|'", "$accept", "sequnused", "seq", "range",
  "matrix_index", "backticks", "history", "expr", "lvalue", "matrixelts",
  "matrixlines", "matrix", "in", "inseq", "compr", "arg", "$@1", "listarg",
  "funcid", "memberid", "definition", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,    59,    44,    61,    38,    62,
      60,    43,    45,    37,    92,    47,    42,   290,    94,    35,
      33,   126,    91,    39,    46,    40,    58,    93,    96,    41,
     124
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    61,    62,    62,    63,    63,    63,    63,    64,    64,
      64,    64,    65,    65,    66,    66,    67,    67,    67,    67,
      67,    67,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    69,
      69,    69,    70,    70,    71,    71,    72,    72,    72,    72,
      72,    72,    73,    74,    74,    74,    74,    75,    76,    76,
      77,    76,    78,    78,    79,    80,    81,    81,    81,    81
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     0,     1,     2,     3,     0,     1,
       3,     2,     5,     3,     1,     2,     1,     2,     2,     2,
       3,     3,     1,     1,     1,     3,     1,     2,     1,     4,
       1,     1,     1,     1,     1,     3,     3,     2,     2,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     2,     2,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     2,
       2,     3,     2,     2,     2,     2,     1,     3,     3,     1,
       2,     3,     1,     3,     3,     3,     2,     5,     3,     3,
       3,     3,     4,     1,     3,     3,     5,     5,     1,     2,
       0,     4,     1,     3,     4,     3,     6,     5,     3,     4
};

/* YYDEFACT[STATE-NAME] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       4,    22,    23,    79,    26,     0,     0,    16,     0,     0,
       0,     0,    24,     4,     0,     0,    28,     5,    31,    32,
      33,    30,    76,    34,     0,     4,    69,    70,    17,    19,
      14,    18,    49,    48,     0,     0,    86,    82,     0,     0,
      27,     0,    98,     5,     0,     0,     1,     3,     6,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    74,
      72,     8,    73,     0,     4,     0,    75,     4,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    37,    38,     0,
       0,    80,     0,    25,     0,    20,    21,    15,    91,    88,
       0,     0,     0,     0,    89,     0,    90,    79,    99,    78,
     100,     4,     4,     7,    51,    50,    53,    54,    55,    56,
      58,    63,    62,    65,    52,    57,    59,    61,    60,    64,
      66,    67,    68,    71,     0,     0,     9,   105,     0,    77,
     108,    46,    47,    39,    40,    41,    42,    43,    45,    44,
      36,    81,    35,   104,     0,     0,    93,     0,    82,    84,
      83,    85,     0,   109,     0,    11,     8,    13,     0,     4,
      29,     4,    87,     0,     0,     0,    97,   101,     0,    10,
     107,   106,     0,    95,    94,    12,    92,     0,    96
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    14,    42,   135,    76,    31,    16,    17,    18,    38,
      39,    19,   156,   157,    20,    44,   162,    45,    21,    22,
      23
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -162
static const yytype_int16 yypact[] =
{
     583,   -29,  -162,   -26,  -162,   583,   583,    45,   583,   583,
      81,    -2,  -162,   549,    31,    36,  -162,   428,   223,     1,
    -162,  -162,  -162,  -162,    41,   549,    93,    93,  -162,   -17,
    -162,    27,   143,    58,    39,    42,  -162,   168,   -15,    48,
    -162,    60,    66,   292,    29,     3,  -162,  -162,   583,   583,
     583,   583,   583,   583,   583,   583,   583,   583,   583,   583,
     583,   583,   583,   583,   583,   583,   583,   583,   583,  -162,
    -162,   566,  -162,    64,   549,    73,  -162,   583,   583,   583,
     583,   583,   583,   583,   583,   583,   583,  -162,  -162,   583,
      75,  -162,   583,  -162,   -25,  -162,    27,  -162,  -162,  -162,
     583,    60,   583,   583,  -162,   583,  -162,  -162,   -38,  -162,
    -162,   583,   549,   428,   470,   470,   505,   505,   505,   505,
     505,    93,    93,    93,   470,   505,   505,   519,   519,    93,
      93,    93,    93,    93,   583,    33,   248,    69,   -19,  -162,
      66,   428,   428,   428,   428,   428,   428,   428,   428,   428,
     428,  -162,   428,    70,   339,   -28,   -13,    61,   428,    79,
     428,    79,   583,    66,    32,   428,   566,  -162,   583,   583,
    -162,   583,  -162,    77,    60,   583,  -162,   428,    68,   428,
      66,    66,   583,  -162,   384,  -162,   428,    60,  -162
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -162,  -162,     9,   -49,   -16,    92,  -162,    -5,   -34,   -86,
    -162,  -162,  -162,  -161,  -162,    14,  -162,   -10,  -162,  -162,
    -162
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -104
static const yytype_int16 yytable[] =
{
      26,    27,    91,    32,    33,    37,   111,   108,    43,    15,
      95,   112,   173,   183,    71,    94,   159,   112,    90,   161,
     102,   103,   174,   175,    71,    24,   188,    40,    90,    25,
     110,    46,  -102,   110,   153,  -103,    -2,    47,    92,   112,
     170,    30,   104,   113,   114,   115,   116,   117,   118,   119,
     120,   121,   122,   123,   124,   125,   126,   127,   128,   129,
     130,   131,   132,   133,   138,  -102,   136,   155,  -103,   166,
      93,    48,    28,   141,   142,   143,   144,   145,   146,   147,
     148,   149,    34,   105,   150,    97,   140,   152,  -102,   107,
     167,  -103,    91,   137,    29,   154,    98,   158,   160,    99,
     158,    48,   139,    30,   151,   106,   169,   171,     1,     2,
       3,     4,    73,    74,    75,   103,    35,   178,   176,   182,
     163,    96,     5,     6,     7,   185,   164,     0,     0,   165,
       8,     9,     0,    10,    11,    12,    13,     0,    36,    91,
     155,    68,     0,    69,    70,    71,    72,    73,    74,    75,
       0,     0,     0,   155,     0,     0,     0,   177,     0,     0,
       0,   136,     0,   179,     0,     0,     0,     0,     0,     0,
     184,     0,     0,   100,     0,     0,     0,   186,   180,     0,
     181,    49,    50,    51,    52,    53,    54,    55,     0,     0,
      56,    57,    58,    69,    70,    71,    72,    73,    74,    75,
       0,     0,     0,     0,     0,     0,    59,    60,    61,    62,
      63,    64,    65,    66,    67,     0,    68,     0,    69,    70,
      71,    72,    73,    74,    75,     0,     0,    77,   101,    78,
      79,    80,    81,    82,    83,    84,     0,     0,     0,     0,
       0,     0,     0,    85,    86,     0,     0,     0,    87,    88,
       0,     0,     0,   168,     0,     0,     0,     0,     0,     0,
      89,    49,    50,    51,    52,    53,    54,    55,     0,     0,
      56,    57,    58,     0,     0,    71,     0,     0,     0,    90,
       0,     0,     0,     0,     0,     0,    59,    60,    61,    62,
      63,    64,    65,    66,    67,     0,    68,     0,    69,    70,
      71,    72,    73,    74,    75,    49,    50,    51,    52,    53,
      54,    55,     0,     0,    56,    57,    58,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      59,    60,    61,    62,    63,    64,    65,    66,    67,     0,
      68,     0,    69,    70,    71,    72,    73,    74,    75,     0,
       0,   109,    49,    50,    51,    52,    53,    54,    55,     0,
       0,    56,    57,    58,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    59,    60,    61,
      62,    63,    64,    65,    66,    67,     0,    68,     0,    69,
      70,    71,    72,    73,    74,    75,   172,    49,    50,    51,
      52,    53,    54,    55,     0,     0,    56,    57,    58,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   187,
       0,     0,    59,    60,    61,    62,    63,    64,    65,    66,
      67,     0,    68,     0,    69,    70,    71,    72,    73,    74,
      75,    49,    50,    51,    52,    53,    54,    55,     0,     0,
      56,    57,    58,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    59,    60,    61,    62,
      63,    64,    65,    66,    67,     0,    68,     0,    69,    70,
      71,    72,    73,    74,    75,    51,    52,    53,    54,    55,
       0,     0,    56,    57,    58,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    60,
      61,    62,    63,    64,    65,    66,    67,     0,    68,     0,
      69,    70,    71,    72,    73,    74,    75,    56,    57,    58,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    56,    57,    58,     0,     0,    62,    63,    64,    65,
      66,    67,     0,    68,     0,    69,    70,    71,    72,    73,
      74,    75,    64,    65,    66,    67,     0,    68,     0,    69,
      70,    71,    72,    73,    74,    75,     1,     2,     3,     4,
       0,     0,     0,     0,     0,     0,     0,    41,     0,     0,
       5,     6,     7,     1,     2,     3,     4,     0,     8,     9,
       0,    10,    11,    12,    13,     0,     0,     5,     6,     7,
       1,     2,     3,     4,   134,     8,     9,     0,    10,    11,
      12,    13,     0,     0,     5,     6,     7,     0,     0,     0,
       0,     0,     8,     9,     0,    10,    11,    12,    13
};

#define yypact_value_is_default(yystate) \
  ((yystate) == (-162))

#define yytable_value_is_error(yytable_value) \
  YYID (0)

static const yytype_int16 yycheck[] =
{
       5,     6,    18,     8,     9,    10,     3,    41,    13,     0,
      27,    36,    40,   174,    52,    25,   102,    36,    56,   105,
      35,    36,    35,    36,    52,    54,   187,    29,    56,    55,
       1,     0,     3,     1,    59,     3,     0,     1,    37,    36,
      59,    58,    57,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    74,    36,    71,   101,    36,    36,
      29,    35,    27,    78,    79,    80,    81,    82,    83,    84,
      85,    86,     1,    35,    89,    58,    77,    92,    59,    29,
      57,    59,   108,    29,    49,   100,    57,   102,   103,    57,
     105,    35,    29,    58,    29,    57,    37,    37,    27,    28,
      29,    30,    54,    55,    56,    36,    35,   166,    57,    42,
     111,    29,    41,    42,    43,    57,   112,    -1,    -1,   134,
      49,    50,    -1,    52,    53,    54,    55,    -1,    57,   155,
     174,    48,    -1,    50,    51,    52,    53,    54,    55,    56,
      -1,    -1,    -1,   187,    -1,    -1,    -1,   162,    -1,    -1,
      -1,   166,    -1,   168,    -1,    -1,    -1,    -1,    -1,    -1,
     175,    -1,    -1,     5,    -1,    -1,    -1,   182,   169,    -1,
     171,    13,    14,    15,    16,    17,    18,    19,    -1,    -1,
      22,    23,    24,    50,    51,    52,    53,    54,    55,    56,
      -1,    -1,    -1,    -1,    -1,    -1,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    48,    -1,    50,    51,
      52,    53,    54,    55,    56,    -1,    -1,     4,    60,     6,
       7,     8,     9,    10,    11,    12,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    20,    21,    -1,    -1,    -1,    25,    26,
      -1,    -1,    -1,     5,    -1,    -1,    -1,    -1,    -1,    -1,
      37,    13,    14,    15,    16,    17,    18,    19,    -1,    -1,
      22,    23,    24,    -1,    -1,    52,    -1,    -1,    -1,    56,
      -1,    -1,    -1,    -1,    -1,    -1,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    48,    -1,    50,    51,
      52,    53,    54,    55,    56,    13,    14,    15,    16,    17,
      18,    19,    -1,    -1,    22,    23,    24,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      48,    -1,    50,    51,    52,    53,    54,    55,    56,    -1,
      -1,    59,    13,    14,    15,    16,    17,    18,    19,    -1,
      -1,    22,    23,    24,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,    48,    -1,    50,
      51,    52,    53,    54,    55,    56,    57,    13,    14,    15,
      16,    17,    18,    19,    -1,    -1,    22,    23,    24,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    35,
      -1,    -1,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,    48,    -1,    50,    51,    52,    53,    54,    55,
      56,    13,    14,    15,    16,    17,    18,    19,    -1,    -1,
      22,    23,    24,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    48,    -1,    50,    51,
      52,    53,    54,    55,    56,    15,    16,    17,    18,    19,
      -1,    -1,    22,    23,    24,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,    48,    -1,
      50,    51,    52,    53,    54,    55,    56,    22,    23,    24,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    22,    23,    24,    -1,    -1,    41,    42,    43,    44,
      45,    46,    -1,    48,    -1,    50,    51,    52,    53,    54,
      55,    56,    43,    44,    45,    46,    -1,    48,    -1,    50,
      51,    52,    53,    54,    55,    56,    27,    28,    29,    30,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    38,    -1,    -1,
      41,    42,    43,    27,    28,    29,    30,    -1,    49,    50,
      -1,    52,    53,    54,    55,    -1,    -1,    41,    42,    43,
      27,    28,    29,    30,    48,    49,    50,    -1,    52,    53,
      54,    55,    -1,    -1,    41,    42,    43,    -1,    -1,    -1,
      -1,    -1,    49,    50,    -1,    52,    53,    54,    55
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    27,    28,    29,    30,    41,    42,    43,    49,    50,
      52,    53,    54,    55,    62,    63,    67,    68,    69,    72,
      75,    79,    80,    81,    54,    55,    68,    68,    27,    49,
      58,    66,    68,    68,     1,    35,    57,    68,    70,    71,
      29,    38,    63,    68,    76,    78,     0,     1,    35,    13,
      14,    15,    16,    17,    18,    19,    22,    23,    24,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    48,    50,
      51,    52,    53,    54,    55,    56,    65,     4,     6,     7,
       8,     9,    10,    11,    12,    20,    21,    25,    26,    37,
      56,    65,    37,    29,    78,    27,    66,    58,    57,    57,
       5,    60,    35,    36,    57,    35,    57,    29,    69,    59,
       1,     3,    36,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    48,    64,    68,    29,    78,    29,
      63,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    29,    68,    59,    68,    69,    73,    74,    68,    70,
      68,    70,    77,    63,    76,    68,    36,    57,     5,    37,
      59,    37,    57,    40,    35,    36,    57,    68,    64,    68,
      63,    63,    42,    74,    68,    57,    68,    35,    74
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  However,
   YYFAIL appears to be in use.  Nevertheless, it is formally deprecated
   in Bison 2.4.2's NEWS entry, where a plan to phase it out is
   discussed.  */

#define YYFAIL		goto yyerrlab
#if defined YYFAIL
  /* This is here to suppress warnings from the GCC cpp's
     -Wunused-macros.  Normally we don't worry about that warning, but
     some users do, and we want to make it easy for users to remove
     YYFAIL uses, which will produce warnings from Bison 2.5.  */
#endif

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (&yylloc, lex, YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (&yylval, &yylloc, YYLEX_PARAM)
#else
# define YYLEX yylex (&yylval, &yylloc, lex)
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value, Location, lex); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, char **lex)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, lex)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    char **lex;
#endif
{
  if (!yyvaluep)
    return;
  YYUSE (yylocationp);
  YYUSE (lex);
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, char **lex)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep, yylocationp, lex)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    char **lex;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, lex);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, char **lex)
#else
static void
yy_reduce_print (yyvsp, yylsp, yyrule, lex)
    YYSTYPE *yyvsp;
    YYLTYPE *yylsp;
    int yyrule;
    char **lex;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %llu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       , &(yylsp[(yyi + 1) - (yynrhs)])		       , lex);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, yylsp, Rule, lex); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (0, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  YYSIZE_T yysize1;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = 0;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - Assume YYFAIL is not used.  It's too flawed to consider.  See
       <http://lists.gnu.org/archive/html/bison-patches/2009-12/msg00024.html>
       for details.  YYERROR is fine as it does not invoke this
       function.
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                yysize1 = yysize + yytnamerr (0, yytname[yyx]);
                if (! (yysize <= yysize1
                       && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                  return 2;
                yysize = yysize1;
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  yysize1 = yysize + yystrlen (yyformat);
  if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
    return 2;
  yysize = yysize1;

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, char **lex)
#else
static void
yydestruct (yymsg, yytype, yyvaluep, yylocationp, lex)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
    YYLTYPE *yylocationp;
    char **lex;
#endif
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (lex);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {
      case 63: /* "seq" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1415 "../src/language/parse.c"
	break;
      case 64: /* "range" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1424 "../src/language/parse.c"
	break;
      case 65: /* "matrix_index" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1433 "../src/language/parse.c"
	break;
      case 66: /* "backticks" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1442 "../src/language/parse.c"
	break;
      case 67: /* "history" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1451 "../src/language/parse.c"
	break;
      case 68: /* "expr" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1460 "../src/language/parse.c"
	break;
      case 69: /* "lvalue" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1469 "../src/language/parse.c"
	break;
      case 70: /* "matrixelts" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1478 "../src/language/parse.c"
	break;
      case 71: /* "matrixlines" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1487 "../src/language/parse.c"
	break;
      case 72: /* "matrix" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1496 "../src/language/parse.c"
	break;
      case 73: /* "in" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1505 "../src/language/parse.c"
	break;
      case 74: /* "inseq" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1514 "../src/language/parse.c"
	break;
      case 75: /* "compr" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1523 "../src/language/parse.c"
	break;
      case 76: /* "arg" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1532 "../src/language/parse.c"
	break;
      case 78: /* "listarg" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1541 "../src/language/parse.c"
	break;
      case 79: /* "funcid" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1550 "../src/language/parse.c"
	break;
      case 80: /* "memberid" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1559 "../src/language/parse.c"
	break;
      case 81: /* "definition" */

/* Line 1391 of yacc.c  */
#line 82 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1391 of yacc.c  */
#line 1568 "../src/language/parse.c"
	break;

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */
#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (char **lex);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */


/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (char **lex)
#else
int
yyparse (lex)
    char **lex;
#endif
#endif
{
/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Location data for the lookahead symbol.  */
YYLTYPE yylloc;

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.
       `yyls': related to locations.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[3];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */
  yyssp = yyss;
  yyvsp = yyvs;
  yylsp = yyls;

#if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  /* Initialize the default location before parsing starts.  */
  yylloc.first_line   = yylloc.last_line   = 1;
  yylloc.first_column = yylloc.last_column = 1;
#endif

/* User initialization code.  */

/* Line 1590 of yacc.c  */
#line 29 "../src/language/parse.y"
{ yylloc.start=yylloc.end=*lex; }

/* Line 1590 of yacc.c  */
#line 1719 "../src/language/parse.c"
  yylsp[0] = yylloc;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;
	YYLTYPE *yyls1 = yyls;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yyls1, yysize * sizeof (*yylsp),
		    &yystacksize);

	yyls = yyls1;
	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
	YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %llu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;
  *++yylsp = yylloc;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:

/* Line 1806 of yacc.c  */
#line 85 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 3:

/* Line 1806 of yacc.c  */
#line 86 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (2)].val); pari_unused_chars=(yylsp[(1) - (2)]).end;YYABORT;}
    break;

  case 4:

/* Line 1806 of yacc.c  */
#line 89 "../src/language/parse.y"
    {(yyval.val)=NOARG((yyloc));}
    break;

  case 5:

/* Line 1806 of yacc.c  */
#line 90 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 6:

/* Line 1806 of yacc.c  */
#line 91 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (2)].val); (yyloc)=(yylsp[(1) - (2)]);}
    break;

  case 7:

/* Line 1806 of yacc.c  */
#line 92 "../src/language/parse.y"
    {(yyval.val)=newnode(Fseq,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 8:

/* Line 1806 of yacc.c  */
#line 95 "../src/language/parse.y"
    { (yyval.val)=newnode(Frange,NOARG((yyloc)),NOARG((yyloc)),&(yyloc)); }
    break;

  case 9:

/* Line 1806 of yacc.c  */
#line 96 "../src/language/parse.y"
    { (yyval.val)=newnode(Frange,(yyvsp[(1) - (1)].val),NOARG((yyloc)),&(yyloc)); }
    break;

  case 10:

/* Line 1806 of yacc.c  */
#line 97 "../src/language/parse.y"
    { (yyval.val)=newnode(Frange,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc)); }
    break;

  case 11:

/* Line 1806 of yacc.c  */
#line 98 "../src/language/parse.y"
    { (yyval.val)=newnode(Frange,NOARG((yyloc)),(yyvsp[(2) - (2)].val),&(yyloc)); }
    break;

  case 12:

/* Line 1806 of yacc.c  */
#line 101 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrix,(yyvsp[(2) - (5)].val),(yyvsp[(4) - (5)].val),&(yyloc));}
    break;

  case 13:

/* Line 1806 of yacc.c  */
#line 102 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrix,(yyvsp[(2) - (3)].val),-1,&(yyloc));}
    break;

  case 14:

/* Line 1806 of yacc.c  */
#line 105 "../src/language/parse.y"
    {(yyval.val)=1;}
    break;

  case 15:

/* Line 1806 of yacc.c  */
#line 106 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (2)].val)+1;}
    break;

  case 16:

/* Line 1806 of yacc.c  */
#line 109 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhist,-1,-1,&(yyloc));}
    break;

  case 17:

/* Line 1806 of yacc.c  */
#line 110 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhist,newintnode(&(yylsp[(2) - (2)])),-1,&(yyloc));}
    break;

  case 18:

/* Line 1806 of yacc.c  */
#line 111 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhist,newnode(Fsmall,-(yyvsp[(2) - (2)].val),-1,&(yyloc)),-1,&(yyloc));}
    break;

  case 19:

/* Line 1806 of yacc.c  */
#line 112 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhisttime,-1,-1,&(yyloc));}
    break;

  case 20:

/* Line 1806 of yacc.c  */
#line 113 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhisttime,newintnode(&(yylsp[(3) - (3)])),-1,&(yyloc));}
    break;

  case 21:

/* Line 1806 of yacc.c  */
#line 114 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhisttime,newnode(Fsmall,-(yyvsp[(3) - (3)].val),-1,&(yyloc)),-1,&(yyloc));}
    break;

  case 22:

/* Line 1806 of yacc.c  */
#line 117 "../src/language/parse.y"
    {(yyval.val)=newintnode(&(yylsp[(1) - (1)]));}
    break;

  case 23:

/* Line 1806 of yacc.c  */
#line 118 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTreal,&(yyloc));}
    break;

  case 24:

/* Line 1806 of yacc.c  */
#line 119 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTreal,&(yyloc));}
    break;

  case 25:

/* Line 1806 of yacc.c  */
#line 120 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffunction,newconst(CSTmember,&(yylsp[(3) - (3)])),
                                                newintnode(&(yylsp[(1) - (3)])),&(yyloc));}
    break;

  case 26:

/* Line 1806 of yacc.c  */
#line 122 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTstr,&(yyloc));}
    break;

  case 27:

/* Line 1806 of yacc.c  */
#line 123 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTquote,&(yyloc));}
    break;

  case 28:

/* Line 1806 of yacc.c  */
#line 124 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 29:

/* Line 1806 of yacc.c  */
#line 125 "../src/language/parse.y"
    {(yyval.val)=newnode(Fcall,(yyvsp[(1) - (4)].val),(yyvsp[(3) - (4)].val),&(yyloc));}
    break;

  case 30:

/* Line 1806 of yacc.c  */
#line 126 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 31:

/* Line 1806 of yacc.c  */
#line 127 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 32:

/* Line 1806 of yacc.c  */
#line 128 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 33:

/* Line 1806 of yacc.c  */
#line 129 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 34:

/* Line 1806 of yacc.c  */
#line 130 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 35:

/* Line 1806 of yacc.c  */
#line 131 "../src/language/parse.y"
    {(yyval.val)=newnode(Fassign,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 36:

/* Line 1806 of yacc.c  */
#line 132 "../src/language/parse.y"
    {(yyval.val)=newnode(Fassign,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 37:

/* Line 1806 of yacc.c  */
#line 133 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPpp,(yyvsp[(1) - (2)].val),-1,&(yyloc));}
    break;

  case 38:

/* Line 1806 of yacc.c  */
#line 134 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPss,(yyvsp[(1) - (2)].val),-1,&(yyloc));}
    break;

  case 39:

/* Line 1806 of yacc.c  */
#line 135 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPme,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 40:

/* Line 1806 of yacc.c  */
#line 136 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPde,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 41:

/* Line 1806 of yacc.c  */
#line 137 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPdre,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 42:

/* Line 1806 of yacc.c  */
#line 138 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPeuce,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 43:

/* Line 1806 of yacc.c  */
#line 139 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPmode,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 44:

/* Line 1806 of yacc.c  */
#line 140 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsle,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 45:

/* Line 1806 of yacc.c  */
#line 141 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsre,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 46:

/* Line 1806 of yacc.c  */
#line 142 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPpe,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 47:

/* Line 1806 of yacc.c  */
#line 143 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPse,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 48:

/* Line 1806 of yacc.c  */
#line 144 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPnb,(yyvsp[(2) - (2)].val),-1,&(yyloc));}
    break;

  case 49:

/* Line 1806 of yacc.c  */
#line 145 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPlength,(yyvsp[(2) - (2)].val),-1,&(yyloc));}
    break;

  case 50:

/* Line 1806 of yacc.c  */
#line 146 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPor,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 51:

/* Line 1806 of yacc.c  */
#line 147 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPand,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 52:

/* Line 1806 of yacc.c  */
#line 148 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPand,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 53:

/* Line 1806 of yacc.c  */
#line 149 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPid,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 54:

/* Line 1806 of yacc.c  */
#line 150 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPeq,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 55:

/* Line 1806 of yacc.c  */
#line 151 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPne,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 56:

/* Line 1806 of yacc.c  */
#line 152 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPge,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 57:

/* Line 1806 of yacc.c  */
#line 153 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPg,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 58:

/* Line 1806 of yacc.c  */
#line 154 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPle,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 59:

/* Line 1806 of yacc.c  */
#line 155 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPl,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 60:

/* Line 1806 of yacc.c  */
#line 156 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPs,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 61:

/* Line 1806 of yacc.c  */
#line 157 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPp,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 62:

/* Line 1806 of yacc.c  */
#line 158 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsl,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 63:

/* Line 1806 of yacc.c  */
#line 159 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsr,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 64:

/* Line 1806 of yacc.c  */
#line 160 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPmod,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 65:

/* Line 1806 of yacc.c  */
#line 161 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPdr,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 66:

/* Line 1806 of yacc.c  */
#line 162 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPeuc,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 67:

/* Line 1806 of yacc.c  */
#line 163 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPd,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 68:

/* Line 1806 of yacc.c  */
#line 164 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPm,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 69:

/* Line 1806 of yacc.c  */
#line 165 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(2) - (2)].val);}
    break;

  case 70:

/* Line 1806 of yacc.c  */
#line 166 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPn,(yyvsp[(2) - (2)].val),-1,&(yyloc));}
    break;

  case 71:

/* Line 1806 of yacc.c  */
#line 167 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPpow,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 72:

/* Line 1806 of yacc.c  */
#line 168 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPtrans,(yyvsp[(1) - (2)].val),-1,&(yyloc));}
    break;

  case 73:

/* Line 1806 of yacc.c  */
#line 169 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPderiv,(yyvsp[(1) - (2)].val),-1,&(yyloc));}
    break;

  case 74:

/* Line 1806 of yacc.c  */
#line 170 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPfact,(yyvsp[(1) - (2)].val),-1,&(yyloc));}
    break;

  case 75:

/* Line 1806 of yacc.c  */
#line 171 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatcoeff,(yyvsp[(1) - (2)].val),(yyvsp[(2) - (2)].val),&(yyloc));}
    break;

  case 76:

/* Line 1806 of yacc.c  */
#line 172 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 77:

/* Line 1806 of yacc.c  */
#line 173 "../src/language/parse.y"
    {(yyval.val)=newnode(Ftag,(yyvsp[(1) - (3)].val),0,&(yyloc));}
    break;

  case 78:

/* Line 1806 of yacc.c  */
#line 174 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(2) - (3)].val);}
    break;

  case 79:

/* Line 1806 of yacc.c  */
#line 177 "../src/language/parse.y"
    {(yyval.val)=newnode(Fentry,newconst(CSTentry,&(yylsp[(1) - (1)])),-1,&(yyloc));}
    break;

  case 80:

/* Line 1806 of yacc.c  */
#line 178 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatcoeff,(yyvsp[(1) - (2)].val),(yyvsp[(2) - (2)].val),&(yyloc));}
    break;

  case 81:

/* Line 1806 of yacc.c  */
#line 179 "../src/language/parse.y"
    {(yyval.val)=newnode(Ftag,(yyvsp[(1) - (3)].val),newconst(CSTentry,&(yylsp[(2) - (3)])),&(yyloc));}
    break;

  case 82:

/* Line 1806 of yacc.c  */
#line 182 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 83:

/* Line 1806 of yacc.c  */
#line 183 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrixelts,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 84:

/* Line 1806 of yacc.c  */
#line 186 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrixlines,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 85:

/* Line 1806 of yacc.c  */
#line 187 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrixlines,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 86:

/* Line 1806 of yacc.c  */
#line 190 "../src/language/parse.y"
    {(yyval.val)=newnode(Fvec,-1,-1,&(yyloc));}
    break;

  case 87:

/* Line 1806 of yacc.c  */
#line 191 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPrange,(yyvsp[(2) - (5)].val),(yyvsp[(4) - (5)].val),&(yyloc));}
    break;

  case 88:

/* Line 1806 of yacc.c  */
#line 192 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmat,-1,-1,&(yyloc));}
    break;

  case 89:

/* Line 1806 of yacc.c  */
#line 193 "../src/language/parse.y"
    {(yyval.val)=newnode(Fvec,(yyvsp[(2) - (3)].val),-1,&(yyloc));}
    break;

  case 90:

/* Line 1806 of yacc.c  */
#line 194 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmat,(yyvsp[(2) - (3)].val),-1,&(yyloc));}
    break;

  case 91:

/* Line 1806 of yacc.c  */
#line 195 "../src/language/parse.y"
    {(yyval.val)=-1; YYABORT;}
    break;

  case 92:

/* Line 1806 of yacc.c  */
#line 198 "../src/language/parse.y"
    {(yyval.val)=newnode(Flistarg,(yyvsp[(4) - (4)].val),(yyvsp[(1) - (4)].val),&(yyloc));}
    break;

  case 93:

/* Line 1806 of yacc.c  */
#line 201 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPcompr,(yyvsp[(1) - (1)].val),-2,&(yyloc));}
    break;

  case 94:

/* Line 1806 of yacc.c  */
#line 202 "../src/language/parse.y"
    {(yyval.val)=newopcall3(OPcompr,(yyvsp[(1) - (3)].val),-2,(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 95:

/* Line 1806 of yacc.c  */
#line 203 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPcomprc,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 96:

/* Line 1806 of yacc.c  */
#line 204 "../src/language/parse.y"
    {(yyval.val)=newopcall3(OPcomprc,(yyvsp[(1) - (5)].val),(yyvsp[(5) - (5)].val),(yyvsp[(3) - (5)].val),&(yyloc));}
    break;

  case 97:

/* Line 1806 of yacc.c  */
#line 207 "../src/language/parse.y"
    {(yyval.val)=addcurrexpr((yyvsp[(4) - (5)].val),(yyvsp[(2) - (5)].val),&(yyloc));}
    break;

  case 98:

/* Line 1806 of yacc.c  */
#line 210 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 99:

/* Line 1806 of yacc.c  */
#line 211 "../src/language/parse.y"
    {(yyval.val)=newnode(Frefarg,(yyvsp[(2) - (2)].val),-1,&(yyloc));}
    break;

  case 100:

/* Line 1806 of yacc.c  */
#line 212 "../src/language/parse.y"
    {if (!pari_once) { yyerrok; } pari_once=1;}
    break;

  case 101:

/* Line 1806 of yacc.c  */
#line 213 "../src/language/parse.y"
    {pari_once=0; (yyval.val)=newopcall(OPcat,(yyvsp[(1) - (4)].val),(yyvsp[(4) - (4)].val),&(yyloc));}
    break;

  case 102:

/* Line 1806 of yacc.c  */
#line 216 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);}
    break;

  case 103:

/* Line 1806 of yacc.c  */
#line 217 "../src/language/parse.y"
    {(yyval.val)=newnode(Flistarg,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 104:

/* Line 1806 of yacc.c  */
#line 220 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffunction,newconst(CSTentry,&(yylsp[(1) - (4)])),(yyvsp[(3) - (4)].val),&(yyloc));}
    break;

  case 105:

/* Line 1806 of yacc.c  */
#line 223 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffunction,newconst(CSTmember,&(yylsp[(3) - (3)])),(yyvsp[(1) - (3)].val),&(yyloc));}
    break;

  case 106:

/* Line 1806 of yacc.c  */
#line 227 "../src/language/parse.y"
    {(yyval.val)=newfunc(CSTentry,&(yylsp[(1) - (6)]),(yyvsp[(3) - (6)].val),(yyvsp[(6) - (6)].val),&(yyloc));}
    break;

  case 107:

/* Line 1806 of yacc.c  */
#line 229 "../src/language/parse.y"
    {(yyval.val)=newfunc(CSTmember,&(yylsp[(3) - (5)]),(yyvsp[(1) - (5)].val),(yyvsp[(5) - (5)].val),&(yyloc));}
    break;

  case 108:

/* Line 1806 of yacc.c  */
#line 230 "../src/language/parse.y"
    {(yyval.val)=newnode(Flambda, (yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));}
    break;

  case 109:

/* Line 1806 of yacc.c  */
#line 231 "../src/language/parse.y"
    {(yyval.val)=newnode(Flambda, (yyvsp[(2) - (4)].val),(yyvsp[(4) - (4)].val),&(yyloc));}
    break;



/* Line 1806 of yacc.c  */
#line 2664 "../src/language/parse.c"
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (&yylloc, lex, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (&yylloc, lex, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval, &yylloc, lex);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  yyerror_range[1] = yylsp[1-yylen];
  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp, yylsp, lex);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;

  yyerror_range[2] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
  *++yylsp = yyloc;

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (&yylloc, lex, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc, lex);
    }
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp, yylsp, lex);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}



/* Line 2067 of yacc.c  */
#line 234 "../src/language/parse.y"


