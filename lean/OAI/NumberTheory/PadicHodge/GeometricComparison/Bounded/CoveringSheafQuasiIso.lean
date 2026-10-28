import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresheafQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction

/-! # Covering Sheaf Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CoveringSheafQuasiIso.BoundedCoveringSheafQuasiIso

noncomputable section

/-! Covering-object detection for the original bounded crystalline
sheafification, including its required coefficient universe lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u z v w

section Coefficients
variable (B : Type u) [CommRing B] (D : Type v) [Category.{w} D]

def coefficients : (Dᵒᵖ ⥤ ModuleCat.{u} B) ⥤
    (Dᵒᵖ ⥤ ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))) :=
  (Functor.whiskeringRight Dᵒᵖ _ _).obj
    (IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B))

instance coefficients_additive : (coefficients B D).Additive where
  map_add := by intros; rfl

instance coefficients_limits : PreservesFiniteLimits (coefficients B D) where
  preservesFiniteLimits T _ _ := by
    dsimp only [coefficients]
    infer_instance

instance coefficients_colimits : PreservesFiniteColimits (coefficients B D) where
  preservesFiniteColimits T _ _ := by
    dsimp only [coefficients]
    infer_instance

instance coefficients_homology : (coefficients B D).PreservesHomology := by infer_instance

theorem coefficients_quasiIso {K H : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u} B) ℕ}
    (φ : K ⟶ H) (h : QuasiIso φ) :
    QuasiIso (((coefficients B D).mapHomologicalComplex (.up ℕ)).map φ) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology φ (coefficients B D) (hφ := h)

end Coefficients

variable (B : Type u) [CommRing B] {C : Type (u + 1)} [Category.{u} C]
  (J : GrothendieckTopology C)
  {K H : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℕ} (φ : K ⟶ H)
  {ι : Type z} (F : ι → C)

theorem restricted (T : C)
    (h : QuasiIso (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B)
      (Over.forget T)).mapHomologicalComplex (.up ℕ)).map φ)) :
    QuasiIso ((((Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).obj
      (Over.forget T).op).mapHomologicalComplex (.up ℕ)).map
        (((coefficients B C).mapHomologicalComplex (.up ℕ)).map φ)) :=
  coefficients_quasiIso B (Over T)
    (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B)
      (Over.forget T)).mapHomologicalComplex (.up ℕ)).map φ) h

theorem quasiIso
    (hcover : ∀ T, IntegralComparison.CoveringObjectsSheafDetection.sieve F T ∈ J T)
    (hlocal : ∀ i, QuasiIso (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B)
      (Over.forget (F i))).mapHomologicalComplex (.up ℕ)).map φ)) :
    QuasiIso (((coefficients B C ⋙ presheafToSheaf J (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map φ) :=
  IntegralComparison.CoveringPresheafQuasiIso.quasiIso.{u + 1, u, z} J (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
    (((coefficients B C).mapHomologicalComplex (.up ℕ)).map φ) F hcover
      (fun i => restricted B φ (F i) (hlocal i))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CoveringSheafQuasiIso.BoundedCoveringSheafQuasiIso
