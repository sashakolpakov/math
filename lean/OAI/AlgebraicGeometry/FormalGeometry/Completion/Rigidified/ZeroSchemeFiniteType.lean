import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductZeroScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts

/-! # Zero Scheme Finite Type -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Local finite type and quasi-compactness of the actual global
zero scheme descend from its normalized-frame charts. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [IsLocallyNoetherian B.left] (D : ProductLine.Construction.RigidifiedProductLine A B)

theorem ProductLine.Construction.RigidifiedProductLine.zeroScheme_localProperty (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ (T : Over (Spec (.of K))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)]
      (a : T ⟶ B), P (D.zeroChart a).hom) : P D.zeroScheme.hom := by
  have := D.zeroSchemeSubfunctor_isRepresentable
  let U := B.left.affineCover
  let T := fun i : U.I₀ => Over.mk (U.f i ≫ B.hom)
  let a := fun i : U.I₀ => (Over.homMk (U.f i) rfl : T i ⟶ B)
  have : ∀ i, IsAffine (T i).left := fun i => inferInstanceAs (IsAffine (B.left.affineCover.X i))
  have : ∀ i, IsNoetherianRing Γ((T i).left, ⊤) := by
    intro i
    have : IsLocallyNoetherian (U.X i) := LocallyOfFiniteType.isLocallyNoetherian (U.f i)
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U.X i)⟩
  let M := fun i => D.zeroChart (a i)
  have : ∀ i, Mono (M i).hom := fun i => D.zeroChart_mono (a i)
  exact RepresentedSubfunctorCharts.Construction.representedSubfunctor_localProperty D.zeroSchemeSubfunctor U M
    (fun i Z j => D.zeroChart_schemeFactorization (a i) Z j) P (fun i => hP (T i) (a i))

instance ProductLine.Construction.RigidifiedProductLine.zeroScheme_locallyOfFiniteType : LocallyOfFiniteType D.zeroScheme.hom :=
  D.zeroScheme_localProperty (@LocallyOfFiniteType) (fun _ _ _ a => D.zeroChart_locallyOfFiniteType a)

instance ProductLine.Construction.RigidifiedProductLine.zeroScheme_quasiCompact : QuasiCompact D.zeroScheme.hom :=
  D.zeroScheme_localProperty (@QuasiCompact) (fun _ _ _ a => D.zeroChart_quasiCompact a)

instance ProductLine.Construction.RigidifiedProductLine.zeroInclusion_mono : Mono D.zeroInclusion :=
  inferInstanceAs (Mono (FamilyLiftFactorization.Construction.compositeFamilyMap B D.zeroScheme))

instance ProductLine.Construction.RigidifiedProductLine.zeroInclusion_left_mono : Mono D.zeroInclusion.left :=
  inferInstanceAs (Mono D.zeroScheme.hom)

instance ProductLine.Construction.RigidifiedProductLine.zeroInclusion_left_quasiCompact : QuasiCompact D.zeroInclusion.left :=
  inferInstanceAs (QuasiCompact D.zeroScheme.hom)

instance ProductLine.Construction.RigidifiedProductLine.zeroSchemeOver_locallyOfFiniteType [LocallyOfFiniteType B.hom] :
    LocallyOfFiniteType D.zeroSchemeOver.hom := by
  change LocallyOfFiniteType (D.zeroScheme.hom ≫ B.hom)
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
