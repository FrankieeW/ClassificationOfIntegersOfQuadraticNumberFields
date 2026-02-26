// Lean compiler output
// Module: ClassificationOfIntegersOfQuadraticNumberFields.Core
// Imports: public import Init public import Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
static lean_once_cell_t lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0;
extern lean_object* lp_mathlib_Rat_commRing;
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lp_mathlib_QuadraticAlgebra_norm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace___boxed(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Rat_instField;
lean_object* lp_mathlib_QuadraticAlgebra_instField___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_instFieldOfIsNonsquareRat___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_instFieldOfIsNonsquareRat(lean_object*, lean_object*);
static lean_object* _init_lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lp_mathlib_Rat_commRing;
x_4 = l_Rat_ofInt(x_1);
x_5 = lean_obj_once(&lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0, &lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0_once, _init_lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0);
x_6 = lp_mathlib_QuadraticAlgebra_norm___redArg(x_4, x_5, x_3);
x_7 = lean_apply_1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_obj_once(&lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0, &lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0_once, _init_lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0);
x_5 = l_Rat_mul(x_4, x_3);
lean_inc(x_2);
x_6 = l_Rat_add(x_2, x_5);
x_7 = l_Rat_add(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_obj_once(&lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0, &lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0_once, _init_lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0);
x_6 = l_Rat_mul(x_5, x_4);
lean_inc(x_3);
x_7 = l_Rat_add(x_3, x_6);
x_8 = l_Rat_add(x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_trace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_instFieldOfIsNonsquareRat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lp_mathlib_Rat_instField;
x_3 = l_Rat_ofInt(x_1);
x_4 = lean_obj_once(&lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0, &lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0_once, _init_lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_norm___closed__0);
x_5 = lp_mathlib_QuadraticAlgebra_instField___redArg(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_instFieldOfIsNonsquareRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Qsqrtd_instFieldOfIsNonsquareRat___redArg(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ClassificationOfIntegersOfQuadraticNumberFields_ClassificationOfIntegersOfQuadraticNumberFields_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
