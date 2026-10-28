import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Polarization
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Fiber Hom Equality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberHomEquality.Construction

noncomputable section

/-!
Compare actual geometric-fiber morphisms. Reducedness of the smooth
source and density of closed points turn the previously proved equality
on point groups into equality of scheme morphisms, enabling transfer of
the field polarization's positivity and kernel type without a new
compatibility hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- On a reduced finite-type scheme over an algebraically closed field,
the rational points determine a morphism into a separated scheme. -/
theorem morphism_eq_of_rational_points
    {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (.of K))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ a : (𝟙_ (Over (Spec (.of K)))) ⟶ X, a ≫ f = a ≫ g) : f = g := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let j := equalizer.ι f g
  have : Surjective j.left := by
    constructor
    intro x
    by_contra hx
    have hclosed : IsClosed (Set.range j.left) := j.left.isClosedEmbedding.isClosed_range
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (Z := (Set.range j.left)ᶜ) ⟨x, hx⟩ hclosed.isOpen_compl.isLocallyClosed
    let a : (𝟙_ (Over (Spec (.of K)))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom z hzc) (pointOfClosedPoint_comp X.hom z hzc)
    let l := equalizer.lift a (h a)
    apply hz
    refine ⟨l.left (IsLocalRing.closedPoint K), ?_⟩
    have hl := congrArg (fun m => m.left (IsLocalRing.closedPoint K)) (equalizer.lift_ι a (h a))
    exact hl.trans (pointOfClosedPoint_apply X.hom z hzc _)
  have : IsIso j.left := isIso_of_isClosedImmersion_of_surjective j.left
  apply Over.OverMorphism.ext
  apply (cancel_epi j.left).mp
  exact congrArg (fun m => m.left) (equalizer.condition f g)

/-- The constructed relative homomorphism restricts to every actual
field-level PoincareBundle polarization map satisfying its pullback identity. -/
theorem relative_polarization_matches_field_morphism
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K))
    (A B AD BD : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (n : ℕ) (hn : 0 < n)
    (f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny A B)
    (fd : BD.toOver ⟶ AD.toOver) [IsMonHom fd]
    (gd : AD.toOver ⟶ BD.toOver) [IsMonHom gd]
    (polarization : A.toOver ⟶ AD.toOver)
    (hfdgd : fd ≫ gd = (𝟙 BD.toOver) ^ n)
    (p : B.toOver ⟶ BD.toOver) [IsMonHom p]
    (hp : f.hom ≫ p ≫ fd = polarization ^ n)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u})
    (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S)
    (fieldPolarization : (Over.pullback s).obj B.toOver ⟶ (Over.pullback s).obj BD.toOver)
    [IsMonHom fieldPolarization]
    (h_PoincareBundle : (Over.pullback s).map f.hom ≫ fieldPolarization ≫ (Over.pullback s).map fd =
      ((Over.pullback s).map polarization) ^ n) :
    (Over.pullback s).map p = fieldPolarization := by
  obtain ⟨_, _, hsurj, hfp, _⟩ := Multiplication.Construction.multiplication_geometry_from_TorsionQuotient B.toOver n
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := B.toOver) base n hn h_TorsionQuotient)
  have : Surjective (((𝟙 B.toOver) ^ n).left) := hsurj
  have : LocallyOfFinitePresentation (((𝟙 B.toOver) ^ n).left) := hfp
  have hpoints := Polarization.Construction.relative_hom_matches_field_polarization n f.hom fd gd polarization hfdgd p hp
    L s (BaseChangePoints.Construction.fieldMorphismOnPoints s fieldPolarization)
    (BaseChangePoints.Construction.field_polarization_identity_on_points s n f.hom fd polarization fieldPolarization h_PoincareBundle)
  have : Smooth ((Over.pullback s).obj B.toOver).hom :=
    inferInstanceAs (Smooth (pullback.snd B.toOver.hom s))
  have : IsReduced ((Over.pullback s).obj B.toOver).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field ((Over.pullback s).obj B.toOver).hom
  have : IsSeparated ((Over.pullback s).obj BD.toOver).hom :=
    inferInstanceAs (IsSeparated (pullback.snd BD.toOver.hom s))
  apply morphism_eq_of_rational_points
  intro a
  obtain ⟨b, hb⟩ := (BaseChangePoints.Construction.pointSectionMap_bijective s B.toOver).2 a
  have h := congrArg (fun q => q b) hpoints
  change b ≫ p = BaseChangePoints.Construction.fieldMorphismOnPoints s fieldPolarization b at h
  have h' := congrArg (BaseChangePoints.Construction.pointSectionMap s BD.toOver) h
  rw [BaseChangePoints.Construction.pointSectionMap_natural, BaseChangePoints.Construction.fieldMorphismOnPoints_section, hb] at h'
  exact h'

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberHomEquality.Construction
