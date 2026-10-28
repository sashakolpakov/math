import OAI.NumberTheory.PadicHodge.IntegralComparison.PoincareAugmentationFormula

/-! # Poincare -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare

noncomputable section

/-!
# IntegralComparison: the canonical integral Poincaré map as a map of additive complexes

Forgetting the coefficient-module structure preserves the proved
homotopy equivalence. The canonical transport of a complex concentrated
in degree zero gives the additive augmentation with its explicit formula.
-/

open _root_.CategoryTheory

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I) [Fintype σ]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
abbrev forgetCoefficients : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} := forget₂ _ _

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare.forgetCoefficients R
local notation "M" => ModuleCat.of R R

def complex : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R G IG γ)

omit [Fintype σ] in
theorem complex_d_apply (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G IG γ n) :
    (complex R σ I δ).d n (n + 1) ω = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R G IG γ n ω := by
  have hd := CochainComplex.of_d
    (fun n => ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G IG γ n))
    (fun n => ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R G IG γ n)) n
  exact congrArg (fun d => d ω) hd

def sourceIso :
    ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ (ModuleCat R)).obj M) ≅
      (CochainComplex.single₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of R) :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app M

def mappedHomotopyEquiv := (F).mapHomotopyEquiv (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.homotopyEquiv R σ I δ)

def augmentation :
    (CochainComplex.single₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of R) ⟶ complex R σ I δ :=
  (sourceIso R).inv ≫ (mappedHomotopyEquiv R σ I δ).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ I δ) := by
  have : QuasiIso (mappedHomotopyEquiv R σ I δ).hom :=
    HomotopyEquiv.quasiIso_hom (mappedHomotopyEquiv R σ I δ)
  exact inferInstanceAs (QuasiIso ((sourceIso R).inv ≫ (mappedHomotopyEquiv R σ I δ).hom))

omit [Fintype σ] in
theorem sourceIso_inv_zero : (sourceIso R).inv.f 0 = 𝟙 (AddCommGrpCat.of R) := by
  exact (HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (ComplexShape.up ℕ) 0 M).trans
    (by
      simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
      rfl)

theorem augmentation_zero (r : R) : (augmentation R σ I δ).f 0 r =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R G IG γ (algebraMap R G r) (fun i : Fin 0 => i.elim0) := by
  change (mappedHomotopyEquiv R σ I δ).hom.f 0 ((sourceIso R).inv.f 0 r) = _
  rw [sourceIso_inv_zero]
  exact PoincareAugmentationFormula.augmentation_zero R σ I δ r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.Poincare
