import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power

/-! # Unramified Torsion Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnramifiedTorsionDetection.Construction

noncomputable section

/-! Invertible torsion in a proper commutative group is unramified.
Its sections are detected by geometric points without any reducedness
or flatness hypothesis on the test scheme or on the torsion scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem unramified_ext_of_field_points {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S)
      (x : Over.mk s ⟶ X), x ≫ f = x ≫ g) : f = g := by
  have hopen : IsOpenImmersion (equalizer.ι f g).left := EtaleDetection.Construction.equalizer_openImmersion f g
  have hsurj : Surjective (equalizer.ι f g).left := by
    constructor
    intro x
    let T : Over S := Over.mk (X.left.fromSpecResidueField x ≫ X.hom)
    let p : T ⟶ X := Over.homMk (X.left.fromSpecResidueField x) rfl
    let l := equalizer.lift p (h (X.left.residueField x) T.hom p)
    let x₀ : Spec (X.left.residueField x) := default
    refine ⟨l.left x₀, ?_⟩
    change (l.left ≫ (equalizer.ι f g).left) x₀ = x
    rw [← Over.comp_left, equalizer.lift_ι]
    exact X.left.fromSpecResidueField_apply x x₀
  have : IsIso (equalizer.ι f g).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi (equalizer.ι f g).left).mp
  exact congrArg Over.Hom.left (equalizer.condition f g)

theorem unramified_ext_of_geometric_points {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
      (x : Over.mk s ⟶ X), x ≫ f = x ≫ g) : f = g :=
  unramified_ext_of_field_points f g (Geometric.Points.Construction.field_points_eq_of_geometric_points f g h)

theorem invertibleTorsion_section_eq_one_of_geometric_points
    {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G] [IsProper G.hom]
    (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    {T : Over S} (z : T ⟶ G) (hz : z ^ n = 1)
    (hgeo : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
      (x : Over.mk s ⟶ T), x ≫ z = 1) : z = 1 := by
  have : FormallyUnramified (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom :=
    TorsionQuotient.Power.PowerGeometry.torsion_formallyUnramified G n hn
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom := TorsionQuotient.Power.PowerGeometry.torsion_isFinite G n hn
  let a := TorsionQuotient.SubgroupFunctor.torsionLift n z hz
  let b := TorsionQuotient.SubgroupFunctor.torsionLift n (1 : T ⟶ G) (one_pow n)
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι G n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 G) ^ n) 1))
  have hab : a = b := by
    apply unramified_ext_of_geometric_points
    intro K _ _ s x
    apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι G n)).mp
    simp only [Category.assoc, a, b, TorsionQuotient.SubgroupFunctor.torsionLift_ι, MonObj.comp_one]
    exact hgeo K s x
  have he := congrArg (fun c => c ≫ TorsionQuotient.SubgroupFunctor.torsionι G n) hab
  simpa only [a, b, TorsionQuotient.SubgroupFunctor.torsionLift_ι] using he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnramifiedTorsionDetection.Construction
