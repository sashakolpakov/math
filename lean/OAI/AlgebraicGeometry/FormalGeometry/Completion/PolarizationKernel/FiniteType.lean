import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Has
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts

/-! # Finite Type -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.FiniteType

noncomputable section

/-! The represented global polarization kernel is of finite type.
Both local finite type and quasi-compactness descend from the actual
normalized-frame charts over affine Noetherian parameter schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

theorem polarizationKernel_localProperty (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ (T : Over (Spec (CommRingCat.of K))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)]
      (a : T ⟶ A), Q (Chart.Construction.polarizationKernelChart A L a).hom) : Q (Has.Construction.polarizationKernel A L).hom := by
  have := PolarizationKernel.Scheme.Construction.polarizationKernelSchemeSubfunctor_isRepresentable A L
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let U := A.left.affineCover
  let T := fun i : U.I₀ => Over.mk (U.f i ≫ A.hom)
  let a := fun i : U.I₀ => (Over.homMk (U.f i) rfl : T i ⟶ A)
  have : ∀ i, IsAffine (T i).left := fun i => inferInstanceAs (IsAffine (A.left.affineCover.X i))
  have : ∀ i, IsNoetherianRing Γ((T i).left, ⊤) := by
    intro i
    have : IsLocallyNoetherian (U.X i) := LocallyOfFiniteType.isLocallyNoetherian (U.f i)
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U.X i)⟩
  let M := fun i => Chart.Construction.polarizationKernelChart A L (a i)
  have : ∀ i, Mono (M i).hom := fun i => Chart.Construction.polarizationKernelChart_mono A L (a i)
  exact RepresentedSubfunctorCharts.Construction.representedSubfunctor_localProperty (PolarizationKernel.Scheme.Construction.polarizationKernelSchemeSubfunctor A L) U M
    (fun i Z j => PolarizationKernel.Scheme.Construction.polarizationKernelChart_schemeFactorization A L (a i) Z j) Q
    (fun i => hQ (T i) (a i))

instance polarizationKernel_locallyOfFiniteType : LocallyOfFiniteType (Has.Construction.polarizationKernel A L).hom :=
  polarizationKernel_localProperty A L (@LocallyOfFiniteType) (fun _ _ _ a =>
    Chart.Construction.polarizationKernelChart_locallyOfFiniteType A L a)

instance polarizationKernel_quasiCompact : QuasiCompact (Has.Construction.polarizationKernel A L).hom :=
  polarizationKernel_localProperty A L (@QuasiCompact) (fun _ _ _ a =>
    Chart.Construction.polarizationKernelChart_quasiCompact A L a)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.FiniteType
