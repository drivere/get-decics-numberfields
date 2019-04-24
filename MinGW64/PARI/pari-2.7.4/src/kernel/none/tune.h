#ifdef LONG_IS_64BIT
#define __MULII_KARATSUBA_LIMIT         23
#define __SQRI_KARATSUBA_LIMIT          36
#define __MULII_FFT_LIMIT             1441
#define __SQRI_FFT_LIMIT              1651
#define __MULRR_MULII_LIMIT            276
#define __Fp_POW_REDC_LIMIT             99
#define __Fp_POW_BARRETT_LIMIT         101
#define __INVNEWTON_LIMIT              656
#define __DIVRR_GMP_LIMIT               -1
#define __EXPNEWTON_LIMIT               66
#define __LOGAGM_LIMIT                  16
#define __LOGAGMCX_LIMIT                13
#define __AGM_ATAN_LIMIT                56
#define __INVMOD_GMP_LIMIT              -1
#define __Flx_MUL_KARATSUBA_LIMIT      147
#define __Flx_SQR_KARATSUBA_LIMIT      330
#define __Flx_MUL_HALFMULII_LIMIT        5
#define __Flx_SQR_HALFSQRI_LIMIT         3
#define __Flx_MUL_MULII_LIMIT         1639
#define __Flx_SQR_SQRI_LIMIT             5
#define __Flx_MUL_MULII2_LIMIT           5
#define __Flx_SQR_SQRI2_LIMIT            8
#define __Flx_INVBARRETT_LIMIT        3577
#define __Flx_DIVREM_BARRETT_LIMIT    2804
#define __Flx_REM_BARRETT_LIMIT       3577
#define __Flx_BARRETT_LIMIT           1623
#define __Flx_HALFGCD_LIMIT             80
#define __Flx_GCD_LIMIT               1890
#define __Flx_EXTGCD_LIMIT             284
#define __FpX_INVBARRETT_LIMIT         254
#define __FpX_DIVREM_BARRETT_LIMIT     292
#define __FpX_REM_BARRETT_LIMIT        306
#define __FpX_BARRETT_LIMIT             85
#define __FpX_HALFGCD_LIMIT             75
#define __FpX_GCD_LIMIT                731
#define __FpX_EXTGCD_LIMIT             117
#define __RgX_MUL_LIMIT                  9
#define __RgX_SQR_LIMIT                 35
#else
#define __MULII_KARATSUBA_LIMIT         18
#define __SQRI_KARATSUBA_LIMIT          27
#define __MULII_FFT_LIMIT             1386
#define __SQRI_FFT_LIMIT              1469
#define __MULRR_MULII_LIMIT            102
#define __Fp_POW_REDC_LIMIT             99
#define __Fp_POW_BARRETT_LIMIT          97
#define __INVNEWTON_LIMIT              380
#define __DIVRR_GMP_LIMIT               -1
#define __EXPNEWTON_LIMIT               66
#define __LOGAGM_LIMIT                  55
#define __LOGAGMCX_LIMIT                58
#define __AGM_ATAN_LIMIT               159
#define __INVMOD_GMP_LIMIT              -1
#define __Flx_MUL_KARATSUBA_LIMIT       85
#define __Flx_SQR_KARATSUBA_LIMIT      159
#define __Flx_MUL_HALFMULII_LIMIT        8
#define __Flx_SQR_HALFSQRI_LIMIT         6
#define __Flx_MUL_MULII_LIMIT          698
#define __Flx_SQR_SQRI_LIMIT          1276
#define __Flx_MUL_MULII2_LIMIT        3755
#define __Flx_SQR_SQRI2_LIMIT         4139
#define __Flx_INVBARRETT_LIMIT        4345
#define __Flx_DIVREM_BARRETT_LIMIT    3942
#define __Flx_REM_BARRETT_LIMIT       3942
#define __Flx_BARRETT_LIMIT            915
#define __Flx_HALFGCD_LIMIT            232
#define __Flx_GCD_LIMIT               7165
#define __Flx_EXTGCD_LIMIT             850
#define __FpX_INVBARRETT_LIMIT         337
#define __FpX_DIVREM_BARRETT_LIMIT     306
#define __FpX_REM_BARRETT_LIMIT        306
#define __FpX_BARRETT_LIMIT            144
#define __FpX_HALFGCD_LIMIT            145
#define __FpX_GCD_LIMIT               1292
#define __FpX_EXTGCD_LIMIT             238
#define __RgX_MUL_LIMIT                  5
#define __RgX_SQR_LIMIT                 26
#endif
