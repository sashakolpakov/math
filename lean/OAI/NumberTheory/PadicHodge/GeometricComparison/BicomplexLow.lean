import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainLow

/-! # Bicomplex Low -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree

noncomputable section

/-! Element formulas in the first three rows of an actual module bicomplex. -/

open _root_.CategoryTheory

universe u v
variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))

def vertical (q j : ℕ) : (B.X q).X j →ₗ[R] (B.X q).X (j + 1) :=
  ((B.X q).d j (j + 1)).hom

def horizontal (q j : ℕ) : (B.X q).X j →ₗ[R] (B.X (q + 1)).X j :=
  ((B.d q (q + 1)).f j).hom

theorem vertical_horizontal (q j : ℕ) (x : (B.X q).X j) :
    vertical B (q + 1) j (horizontal B q j x) =
      horizontal B q (j + 1) (vertical B q j x) := by
  exact congrArg (fun g => g.hom x) ((B.d q (q + 1)).comm j (j + 1))

theorem horizontal_horizontal (q j : ℕ) (x : (B.X q).X j) :
    horizontal B (q + 1) j (horizontal B q j x) = 0 := by
  exact congrArg (fun g => (g.f j).hom x) (B.d_comp_d q (q + 1) (q + 1 + 1))

theorem vertical_vertical (q j : ℕ) (x : (B.X q).X j) :
    vertical B q (j + 1) (vertical B q j x) = 0 := by
  exact congrArg (fun g => g.hom x) ((B.X q).d_comp_d j (j + 1) (j + 1 + 1))

variable {B} {C : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)} (f : B ⟶ C)

def component (q j : ℕ) : (B.X q).X j →ₗ[R] (C.X q).X j :=
  ((f.f q).f j).hom

theorem component_vertical (q j : ℕ) (x : (B.X q).X j) :
    component f q (j + 1) (vertical B q j x) =
      vertical C q j (component f q j x) :=
  (congrArg (fun g => g.hom x) ((f.f q).comm j (j + 1))).symm

theorem component_horizontal (q j : ℕ) (x : (B.X q).X j) :
    component f (q + 1) j (horizontal B q j x) =
      horizontal C q j (component f q j x) :=
  (congrArg (fun g => (g.f j).hom x) (f.comm q (q + 1))).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree
