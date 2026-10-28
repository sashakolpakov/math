import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseExtension
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # Forms Coefficient Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsCoefficientMap

noncomputable section

/-!
# IntegralComparison: actual PD differential forms under simultaneous coefficient change

A divided-power algebra map and an extension of the coefficient ring
induce the canonical map on relative forms. Its formula on differential
symbols proves compatibility with exterior differentiation.
-/

open _root_.CategoryTheory

universe u

variable (R S A C : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
  (I : Ideal A) (δI : DividedPowers I) (J : Ideal C) (δJ : DividedPowers J)
  (f : A →ₐ[R] C) (hf : DividedPowers.IsDPMorphism δI δJ f.toRingHom)

def formsMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form S C J δJ n :=
  ((FormsBaseExtension.formsMap R S C J δJ n).restrictScalars R).comp
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n)

theorem formsMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsMap R S A C I δI J δJ f hf n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol S C J δJ (f a) (fun i => f (v i)) := by
  change FormsBaseExtension.formsMap R S C J δJ n
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol, FormsBaseExtension.formsMap_symbol]
  rfl

theorem formsMap_smul (n : ℕ) (a : A) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n) :
    formsMap R S A C I δI J δJ f hf n (a • ω) =
      f a • formsMap R S A C I δI J δJ f hf n ω := by
  change FormsBaseExtension.formsMap R S C J δJ n
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n (a • ω)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul, map_smul]
  rfl

theorem formsMap_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n) :
    formsMap R S A C I δI J δJ f hf (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δI n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential S C J δJ n (formsMap R S A C I δI J δJ f hf n ω) := by
  change FormsBaseExtension.formsMap R S C J δJ (n + 1)
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δI n ω)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_differential, FormsBaseExtension.formsMap_differential]
  rfl

/-- Differential symbols determine every additive map out of the actual form module. -/
theorem addHom_ext (n : ℕ) {M : Type*} [AddCommMonoid M]
    (g h : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n →+ M)
    (hs : ∀ (a : A) (v : Fin n → A),
      g (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v) = h (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v)) : g = h := by
  apply AddMonoidHom.ext
  intro ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI n) ω
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a => exact hs a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsCoefficientMap
