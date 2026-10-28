import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSquare
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.QuasiIso

/-! # Cone Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeQuasiIso

noncomputable section

/-! A genuine isomorphism square of presheaf-complex cones preserves
the quasi-isomorphism property of their original Čech augmentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  {M N : CochainComplex A ℕ} {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ}
  (α : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ K)
  (β : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj N ⟶ L)
  (e : M ≅ N) (t : K ≅ L)
  (h : α ≫ t.hom = ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).map e.hom ≫ β)

local notation "D" => HomologicalComplex.complexOfFunctorsToFunctorToComplex

def map := GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((D).obj K) M ((D).map α)

include h in
omit [Finite ι] in
theorem square : ConeQuasiIso.map U α ≫
    (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map ((D).map t.hom) = e.hom ≫ ConeQuasiIso.map U β := by
  apply GeometricComparison.CechCone.TotalSquare.CechConeTotalConeSquare.natural
  exact (congrArg (D).map h).trans (by rw [Functor.map_comp]; rfl)

omit [Finite ι] in
include h in
theorem quasiIso (hβ : QuasiIso (ConeQuasiIso.map U β)) : QuasiIso (ConeQuasiIso.map U α) := by
  let ti := (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).mapIso ((D).mapIso t)
  have htq : QuasiIso ti.hom := by
    change QuasiIso (((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).mapIso ((D).mapIso t)).hom)
    infer_instance
  have ht : QuasiIso (ConeQuasiIso.map U α ≫ ti.hom) := by
    rw [show ConeQuasiIso.map U α ≫ ti.hom = e.hom ≫ ConeQuasiIso.map U β from square U α β e t h]
    exact quasiIso_comp e.hom (ConeQuasiIso.map U β) (hφ' := hβ)
  exact (quasiIso_iff_comp_right (ConeQuasiIso.map U α) ti.hom (hφ' := htq)).mp ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeQuasiIso
