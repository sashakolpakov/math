import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntersectionRecoveryTransformation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionColimit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramGlobalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing

/-! # Glued Intersection Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The glued intersection scheme recovers the original scheme by base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : FiniteIntersection.IntersectionModel.FiniteIntersectionModel X)
variable (D : Subalgebra M.coefficients R)
variable [(M.baseChangedSchemeFunctor D ⋙ Scheme.forget).IsLocallyDirected]

local instance FiniteIntersection.IntersectionModel.FiniteIntersectionModel.original_scheme_arrow_open {S T : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : S ⟶ T) :
    IsOpenImmersion ((ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))).map h) :=
  ReferenceIntersectionFunctor.originalIntersectionFunctor_open X h

def FiniteIntersection.IntersectionModel.FiniteIntersectionModel.recoveredIntersectionMap : X.left ⟶ colimit (M.baseChangedSchemeFunctor D) :=
  (ReferenceIntersectionColimit.originalIntersectionColimitIso X).inv ≫
    Cartesian.DiagramGluing.cartesianDiagramGluedMap (ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R)))
      (M.baseChangedSchemeFunctor D) (M.intersectionRecoveryNat D) (M.intersectionRecoveryNat_equifibered D)

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.recoveredIntersectionMap_isPullback :
    IsPullback (M.recoveredIntersectionMap D) X.hom
      (Smooth.DiagramGluing.smoothDiagramGluedMap (C := D) (M.baseChangedFunctor D))
      (Spec.map (CommRingCat.ofHom D.val.toRingHom)) := by
  let F := ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))
  let G := M.baseChangedSchemeFunctor D
  let q := M.intersectionRecoveryNat D
  let hq := M.intersectionRecoveryNat_equifibered D
  have H := Cartesian.DiagramGlobalRecovery.cartesianDiagramGluedMap_base_isPullback F G q hq
    ((ReferenceIntersectionColimit.originalIntersectionColimitIso X).hom ≫ X.hom)
    (Smooth.DiagramGluing.smoothDiagramGluedMap (C := D) (M.baseChangedFunctor D))
    (Spec.map (CommRingCat.ofHom D.val.toRingHom)) (fun S => by
      let qi : F.obj S ⟶ G.obj S := M.chartBaseChangeRecovery D S
      have ho := ReferenceIntersectionColimit.originalIntersectionColimitIso_ι_base X S
      have hn := Smooth.DiagramGluing.smoothDiagramGluedMap_ι (C := D) (M.baseChangedFunctor D) S
      exact (congrArg₂ (fun (a : F.obj S ⟶ Spec (.of R)) (b : G.obj S ⟶ Spec (.of D)) =>
        IsPullback qi a b (Spec.map (CommRingCat.ofHom D.val.toRingHom))) ho hn).mpr
        (M.chartBaseChangeRecovery_isPullback D S))
  apply H.of_iso (ReferenceIntersectionColimit.originalIntersectionColimitIso X) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change _ ≫ 𝟙 _ = (ReferenceIntersectionColimit.originalIntersectionColimitIso X).hom ≫
    ((ReferenceIntersectionColimit.originalIntersectionColimitIso X).inv ≫ _)
    dsimp only [F, G, q, hq]
    simp
  · simp
  · simp
  · simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
