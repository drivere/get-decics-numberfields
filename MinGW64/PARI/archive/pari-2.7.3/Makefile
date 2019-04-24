# This file was created by Configure. All changes made will be lost
# next time Configure is run.
#
SHELL = /bin/sh
VERS = pari-2.7.3 released
TAG=release-2-7-3

dft target::
	@echo "Main targets: we suggest 'make all', then 'make install' as root"
	@echo "    all                    Compilation + Documentation"
	@echo "    gp                     Compilation"
	@echo "    bench                  Compilation + Quick test"
	@echo "    dobench                Quick test only"
	@echo "    doc                    Documentation only"
	@echo "    install                Installation"
	@echo "    clean, cleantest       Clean up"
	@echo "For pari maintainers:"
	@echo "    dbg                    Compile gp binary suitable for debugging"
	@echo "    prf                    Compile gp binary suitable for profiling"
	@echo "    gcov                   Compile gp binary for test coverage reporting"
	@echo "    alpha, beta, release   Tarfile for official source distribution"
	@echo "    snapshot, distrib      Tarfile for source snapshot"
	@echo "    nsis                   Create a NSIS installer for win32"
	@echo "    ctags                  Generate VI/VIM tags file in ./src"
	@echo "    etags                  Generate Emacs  tags file in ./src"
	@echo "    tune                   Generate tuning utility"
	@echo "    test-all               Thorough regression tests (slow)"

all::
	@$(MAKE) gp
	@-cd doc && $(MAKE) doc

gp bench test-kernel test-all install cleanall cleanobj cleantest nsis install-bin install-doc install-docpdf install-nodata install-data install-lib-sta install-bin-sta dobench dyntest-all statest-all tune test-addprimes test-agm test-analyz test-apply test-arith test-aurifeuille test-bern test-bessel test-bestappr test-bit test-bnfisintnorm test-bnr test-bnrL1 test-characteristic test-charpoly test-chinese test-cmp test-combinat test-compat test-concat test-content test-contfrac test-cxtrigo test-cyclo test-debugger test-deriv test-det test-diffop test-digits test-dirmul test-disc test-div test-ell test-ellanal test-ellff test-ellglobalred test-elliptic test-ellsea test-ellweilpairing test-equal test-err test-exact0 test-extract test-factor test-factorint test-factormod test-ff test-ffisom test-for test-galois test-galoisinit test-galpol test-gamma test-gcdext test-genus2red test-graph test-help test-history test-ideal test-idealappr test-idealramgroups test-incgam test-interpol test-intnum test-ispower test-isprime test-iterator test-krasner test-lambert test-lex test-lift test-lindep test-linear test-list test-lll test-log test-logint test-mat test-mathnf test-matsnf test-member test-minim test-minmax test-modfun test-modpr test-modular test-multiif test-multivar-mul test-nf test-nffactor test-nfhilbert test-nfields test-nfrootsof1 test-norm test-number test-objets test-op test-orthopol test-padic test-partition test-pol test-polmod test-polred test-polygonal test-polylog test-polyser test-pow test-prec test-prime test-primes test-print test-printf test-program test-qf test-qfb test-qfbsolve test-qfisom test-quad test-quadclassunit test-quadray test-random test-ranges test-real test-resultant test-rfrac test-rnf test-rnfkummer test-round test-round4 test-select test-ser test-set test-size test-sort test-sqrtn test-stark test-str test-subcyclo test-subfields test-subgroup test-subst test-sumdedekind test-sumdiv test-sumformal test-sumiter test-thue test-trans test-trans2 test-valuation test-variable test-whatnow test-zetak test-zn test-zncoppersmith test-ploth test-io test-parallel test-time test-env dotest-addprimes dotest-agm dotest-analyz dotest-apply dotest-arith dotest-aurifeuille dotest-bern dotest-bessel dotest-bestappr dotest-bit dotest-bnfisintnorm dotest-bnr dotest-bnrL1 dotest-characteristic dotest-charpoly dotest-chinese dotest-cmp dotest-combinat dotest-compat dotest-concat dotest-content dotest-contfrac dotest-cxtrigo dotest-cyclo dotest-debugger dotest-deriv dotest-det dotest-diffop dotest-digits dotest-dirmul dotest-disc dotest-div dotest-ell dotest-ellanal dotest-ellff dotest-ellglobalred dotest-elliptic dotest-ellsea dotest-ellweilpairing dotest-equal dotest-err dotest-exact0 dotest-extract dotest-factor dotest-factorint dotest-factormod dotest-ff dotest-ffisom dotest-for dotest-galois dotest-galoisinit dotest-galpol dotest-gamma dotest-gcdext dotest-genus2red dotest-graph dotest-help dotest-history dotest-ideal dotest-idealappr dotest-idealramgroups dotest-incgam dotest-interpol dotest-intnum dotest-ispower dotest-isprime dotest-iterator dotest-krasner dotest-lambert dotest-lex dotest-lift dotest-lindep dotest-linear dotest-list dotest-lll dotest-log dotest-logint dotest-mat dotest-mathnf dotest-matsnf dotest-member dotest-minim dotest-minmax dotest-modfun dotest-modpr dotest-modular dotest-multiif dotest-multivar-mul dotest-nf dotest-nffactor dotest-nfhilbert dotest-nfields dotest-nfrootsof1 dotest-norm dotest-number dotest-objets dotest-op dotest-orthopol dotest-padic dotest-partition dotest-pol dotest-polmod dotest-polred dotest-polygonal dotest-polylog dotest-polyser dotest-pow dotest-prec dotest-prime dotest-primes dotest-print dotest-printf dotest-program dotest-qf dotest-qfb dotest-qfbsolve dotest-qfisom dotest-quad dotest-quadclassunit dotest-quadray dotest-random dotest-ranges dotest-real dotest-resultant dotest-rfrac dotest-rnf dotest-rnfkummer dotest-round dotest-round4 dotest-select dotest-ser dotest-set dotest-size dotest-sort dotest-sqrtn dotest-stark dotest-str dotest-subcyclo dotest-subfields dotest-subgroup dotest-subst dotest-sumdedekind dotest-sumdiv dotest-sumformal dotest-sumiter dotest-thue dotest-trans dotest-trans2 dotest-valuation dotest-variable dotest-whatnow dotest-zetak dotest-zn dotest-zncoppersmith dotest-ploth dotest-io dotest-parallel dotest-time dotest-env::
	@dir=`config/objdir`; echo "Making $@ in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure first!"; exit 1; fi;\
	cd $$dir && $(MAKE) $@

dbg gp.dbg::
	@dir=`config/objdir`.dbg; echo "Making gp in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure -g first!"; exit 1; fi;\
	cd $$dir && $(MAKE) gp

prf gp.prf::
	@dir=`config/objdir`.prf; echo "Making gp in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure -pg first!"; exit 1; fi;\
	cd $$dir && $(MAKE) gp

gcov gp.gcov::
	@dir=`config/objdir`.gcov; echo "Making gp in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure -gcov first!"; exit 1; fi;\
	cd $$dir && $(MAKE) gp

doc docps docpdf gpman cleandoc::
	cd doc && $(MAKE) $@

clean:: cleandoc cleanall

clean.dbg::
	@dir=`config/objdir`.dbg; echo "Making clean in $$dir";\
	 if test ! -d $$dir; then echo "Nothing to be done"; exit 1; fi;\
	cd $$dir && $(MAKE) clean

clean.prf::
	@dir=`config/objdir`.prf; echo "Making clean in $$dir";\
	 if test ! -d $$dir; then echo "Nothing to be done"; exit 1; fi;\
	cd $$dir && $(MAKE) clean

clean.gcov::
	@dir=`config/objdir`.gcov; echo "Making clean in $$dir";\
	 if test ! -d $$dir; then echo "Nothing to be done"; exit 1; fi;\
	cd $$dir && $(MAKE) clean

bench.dbg::
	@dir=`config/objdir`.dbg; echo "Making bench in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure -g first!"; exit 1; fi;\
	cd $$dir && $(MAKE) bench

bench.prf::
	@dir=`config/objdir`.prf; echo "Making bench in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure -pg first!"; exit 1; fi;\
	cd $$dir && $(MAKE) bench

bench.gcov::
	@dir=`config/objdir`.gcov; echo "Making bench in $$dir";\
	 if test ! -d $$dir; then echo "Please run Configure -gcov first!"; exit 1; fi;\
	cd $$dir && $(MAKE) bench

distrib:
	config/settar $(VERS) released

alpha:
	config/settar $(VERS) alpha
beta:
	config/settar $(VERS) beta
release:
	config/settar $(VERS) released
snapshot:
	config/settar $(VERS) snapshot

dosdistrib: gpman
	-zip -kr GPB_273.ZIP GP.EXE README README.DOS ../EMX/README.DOC ../RSX/README.TXT
	-zip -k GPD_273.ZIP doc/*.tex doc/gphelp doc/gp.man examples misc/gprc* misc/gpalias

etags:
	config/make_tags --emacs "/home/eric/BOINC_Project/MinGW64/PARI/pari-2.7.2/src"

ctags:
	config/make_tags --vi "/home/eric/BOINC_Project/MinGW64/PARI/pari-2.7.2/src"

checkspaces:
	config/checkspaces

