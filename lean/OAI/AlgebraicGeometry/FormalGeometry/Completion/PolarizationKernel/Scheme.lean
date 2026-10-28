import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.ChartRepresentation
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSubfunctor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorSchemeGluing

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Scheme

noncomputable section

/-! The actual polarization kernel is represented by a scheme, obtained
by gluing the derived finite-type normalized-frame charts. -/

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

def polarizationKernelSchemeSubfunctor : Subfunctor (yoneda.obj A.left) :=
  OverSubfunctor.Construction.overSubfunctor (Functor.Construction.polarizationKernelSubfunctor A L)

theorem polarizationKernelSchemeSubfunctor_isSheaf :
    Presieve.IsSheaf Scheme.zariskiTopology (polarizationKernelSchemeSubfunctor A L).toFunctor :=
  Presieve.isSheaf_of_le _
    (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
      (OverSubfunctor.Construction.overSubfunctor_isSheaf (Functor.Construction.polarizationKernelSubfunctor A L) Scheme.fppfTopology
        (Functor.Construction.polarizationKernelSubfunctor_isSheaf A L))

theorem polarizationKernelChart_schemeFactorization
    {T : Over (Spec (CommRingCat.of K))} [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)]
    (a : T ⟶ A) (Z : Scheme.{u}) (j : Z ⟶ T.left) :
    (j ≫ a.left) ∈ (polarizationKernelSchemeSubfunctor A L).obj (op Z) ↔
      ∃ z : Z ⟶ (Chart.Construction.polarizationKernelChart A L a).left, z ≫ (Chart.Construction.polarizationKernelChart A L a).hom = j := by
  let U := Over.mk (j ≫ T.hom)
  let f : U ⟶ T := Over.homMk j rfl
  have hp := OverSubfunctor.Construction.overSubfunctor_mem (Functor.Construction.polarizationKernelSubfunctor A L) (f ≫ a)
  constructor
  · intro h
    obtain ⟨p⟩ := (KernelSheaf.Construction.polarizationKernelChart_hasLift_iff_relative_zero A L a f).mpr (hp.mp h)
    exact ⟨p.left, p.w⟩
  · rintro ⟨z, hz⟩
    exact hp.mpr ((KernelSheaf.Construction.polarizationKernelChart_hasLift_iff_relative_zero A L a f).mp ⟨Over.homMk z hz⟩)

theorem polarizationKernelSchemeSubfunctor_isRepresentable :
    (polarizationKernelSchemeSubfunctor A L).toFunctor.IsRepresentable := by
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
  exact SubfunctorSchemeGluing.Construction.subfunctor_isRepresentable_of_openCover (polarizationKernelSchemeSubfunctor A L) U M
    (fun i Z j => polarizationKernelChart_schemeFactorization A L (a i) Z j)
    (polarizationKernelSchemeSubfunctor_isSheaf A L)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Scheme
