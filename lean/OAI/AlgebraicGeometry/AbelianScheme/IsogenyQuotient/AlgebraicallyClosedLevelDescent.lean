import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedFinitePoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus

/-! # Algebraically Closed Level Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedLevelDescent.Construction

noncomputable section

/-! The specified full ordered level descends across an extension of
an algebraically closed characteristic-zero field. Its actual finite
frame parameter recovers the original level on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover

set_option backward.isDefEq.respectTransparency false in
theorem fullLevel_identity_pullback_transport
    {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (α : A.FullLevel N) :
    (α.pullback (𝟙 S)).transport A.pullbackIdIso = α := by
  apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  apply Over.OverMorphism.ext
  change ((α.pullback (𝟙 S)).hom.app (.op T) c).val.left ≫ A.pullbackIdIso.hom.left = _
  rw [A.pullbackIdIso_hom_left]
  exact (congrArg Over.Hom.left (α.pullback_basis (𝟙 S) T c)).trans
    (α.basis_mapId_left T c)

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_fullLevel_descends
    {k K : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field K]
    {g N : ℕ} [NeZero N] (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (u : Spec (.of K) ⟶ Spec (.of k)) (β : (A.pullback u).FullLevel N) :
    ∃ α : A.FullLevel N, α.pullback u = β := by
  let p := 𝟙 (Spec (.of k))
  let X := AbelianModuli.ReferenceFamily.Frame.Locus.LevelCover.fullFrameScheme A p (N := N)
  have : IsFinite X.hom := (AbelianModuli.ReferenceFamily.Frame.Locus.LevelCover.fullFrameScheme_finite_etale A p).1
  let T : Over (Spec (.of k)) := Over.mk u
  let U : Over (Spec (.of k)) := Over.mk (𝟙 _)
  let v : T ⟶ U := Over.homMk u (Category.comp_id u)
  let f : T ⟶ X := (AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.fullFramePointsEquiv A p T).symm β
  obtain ⟨z, hz⟩ := (AlgebraicallyClosedFinitePoints.Construction.algebraicallyClosed_quasiFinite_points_bijective X u).surjective f
  let γ := AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.fullFramePointsEquiv A p U z
  let α := γ.transport A.pullbackIdIso
  have hγ : α.pullback (𝟙 (Spec (.of k))) = γ := by
    apply AbelianModuli.ReferenceFamily.Level.IsoCalculus.fullLevel_transport_injective A.pullbackIdIso
    exact fullLevel_identity_pullback_transport A α
  refine ⟨α, ?_⟩
  calc
    α.pullback u = (α.pullback (𝟙 (Spec (.of k)))).restrict v := (α.restrict_pullback v).symm
    _ = γ.restrict v := congrArg (fun a => a.restrict v) hγ
    _ = AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.fullFramePointsEquiv A p T (v ≫ z) := (AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.fullFramePointsEquiv_natural A p v z).symm
    _ = β := (congrArg (AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.fullFramePointsEquiv A p T) hz).trans
      ((AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.fullFramePointsEquiv A p T).apply_symm_apply β)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedLevelDescent.Construction
