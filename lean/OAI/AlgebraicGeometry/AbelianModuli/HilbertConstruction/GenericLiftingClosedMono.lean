import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.GenericLifting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiFiniteQuasiProjectivity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianSpecializationClosed
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Generic Lifting Closed Mono -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A finite-type monomorphism with integral local lifting is closed.
An ample compactification reduces this to specialization of its open image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianSpecializationClosed.Geometric

theorem Local.GenericLifting.LocalGenericLifting.compactification_range_stable
    {X Y Z : Scheme.{0}} {f : X ⟶ Y} [Mono f]
    (h : Local.GenericLifting.LocalGenericLifting f) [IsNoetherian Z]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsSeparated p]
    (hj : j ≫ p = f) : StableUnderSpecialization (Set.range j) := by
  intro z z' hzz
  rintro ⟨x, rfl⟩
  let C := Picard.ThetaConstruction.PointClosureLocalTest.Geometric.pointClosure (j x)
  let i := Picard.ThetaConstruction.PointClosureLocalTest.Geometric.pointClosureInclusion (j x)
  let : IsIntegral C := Picard.ThetaConstruction.PointClosureLocalTest.Geometric.pointClosure_integral (j x)
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian i
  have hz' : z' ∈ Set.range i := by
    rw [Picard.ThetaConstruction.PointClosureLocalTest.Geometric.pointClosureInclusion_range]
    exact specializes_iff_mem_closure.mp hzz
  obtain ⟨c, hc⟩ := hz'
  let R := C.presheaf.stalk c
  let : IsDomain R := inferInstanceAs (IsDomain (C.presheaf.stalk c))
  let T := Spec R
  let : IsAffine T := inferInstanceAs (IsAffine (Spec R))
  let : IsLocallyNoetherian T := inferInstanceAs (IsLocallyNoetherian (Spec R))
  let : IsIntegral T := inferInstanceAs (IsIntegral (Spec R))
  let : IsLocalRing Γ(T, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing R
  let : IsNoetherianRing Γ(T, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing R
  let u : T ⟶ Z := C.fromSpecStalk c ≫ i
  have hu : u (genericPoint T) = j x := by
    change i (C.fromSpecStalk c (genericPoint (Spec R))) = j x
    rw [Picard.ThetaConstruction.PointClosureLocalTest.Geometric.integral_fromSpecStalk_generic]
    exact Picard.ThetaConstruction.PointClosureLocalTest.Geometric.pointClosure_generic (j x)
  have hp : (u ≫ p) (genericPoint T) = f x := by
    calc
      (u ≫ p) (genericPoint T) = p (j x) := congrArg p hu
      _ = f x := congrArg (fun k : X ⟶ Y => k x) hj
  obtain ⟨w, hw⟩ := h T (u ≫ p) x hp
  let U : T.Opens := u ⁻¹ᵁ j.opensRange
  have hη : genericPoint T ∈ U := by
    change u (genericPoint T) ∈ Set.range j
    exact hu ▸ Set.mem_range_self x
  have hU : Set.range (U.ι ≫ u) ⊆ Set.range j := by
    rintro _ ⟨t, rfl⟩
    exact t.property
  let v : U.toScheme ⟶ X := IsOpenImmersion.lift j (U.ι ≫ u) hU
  have hv : v ≫ j = U.ι ≫ u := IsOpenImmersion.lift_fac j (U.ι ≫ u) hU
  have hvw : v = U.ι ≫ w := by
    apply (cancel_mono f).mp
    calc
      v ≫ f = v ≫ j ≫ p := by rw [hj]
      _ = (U.ι ≫ u) ≫ p := by rw [← Category.assoc, hv]
      _ = (U.ι ≫ w) ≫ f := by
        simpa only [Category.assoc] using congrArg (fun b : T ⟶ Y => U.ι ≫ b) hw.symm
  let : IsDominant U.ι := by
    apply Opens.isDominant_ι
    intro t
    exact closure_mono (Set.singleton_subset_iff.mpr hη)
      (specializes_iff_mem_closure.mp (genericPoint_specializes t))
  have hue : u = w ≫ j := by
    refine ext_of_isDominant_of_isSeparated p ?_ U.ι ?_
    · exact hw.symm.trans ((Category.assoc w j p).trans (congrArg (fun b => w ≫ b) hj)).symm
    · exact hv.symm.trans (by rw [hvw, Category.assoc])
  refine ⟨w (IsLocalRing.closedPoint R), ?_⟩
  have he := congrArg (fun k : T ⟶ Z => k (IsLocalRing.closedPoint R)) hue.symm
  apply he.trans
  change i (C.fromSpecStalk c (IsLocalRing.closedPoint R)) = z'
  rw [Scheme.fromSpecStalk_closedPoint]
  exact hc

theorem Local.GenericLifting.LocalGenericLifting.closedImmersion_of_affine
    {X Y : Scheme.{0}} [IsAffine Y] [IsNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [Mono f]
    (h : Local.GenericLifting.LocalGenericLifting f) : IsClosedImmersion f := by
  let : LocallyQuasiFinite f := UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified f
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨Q⟩ := (ReferenceFamily.AmpleQuasiFinitePullback.ample_pullback_separated_quasiFinite f
    (Line.Bundles.LineBundle.trivial Y) (Line.Bundles.LineBundle.trivial_isAmple Y)).exists_quasiProjectivePresentation f
  let : IsProper Q.compactification.hom := Q.projective.proper
  let : IsLocallyNoetherian Q.compactification.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q.compactification.hom
  let : CompactSpace Q.compactification.left :=
    QuasiCompact.compactSpace_of_compactSpace Q.compactification.hom
  let : IsNoetherian Q.compactification.left := ⟨⟩
  have hs := h.compactification_range_stable Q.embedding.left Q.compactification.hom Q.embedding.w
  have hc : IsClosed (Set.range Q.embedding.left) :=
    Picard.ThetaConstruction.NoetherianSpecializationClosed.Geometric.isClosed_of_isOpen_stableUnderSpecialization Q.embedding.left.isOpenEmbedding.isOpen_range hs
  let : IsClosedImmersion Q.embedding.left := IsClosedImmersion.of_isPreimmersion _ hc
  have hQ : Q.embedding.left ≫ Q.compactification.hom = f := Q.embedding.w
  have hf : IsProper f := hQ ▸
    inferInstanceAs (IsProper (Q.embedding.left ≫ Q.compactification.hom))
  exact (IsClosedImmersion.iff_isProper_and_mono f).mpr ⟨hf, inferInstance⟩

theorem Local.GenericLifting.LocalGenericLifting.closedImmersion
    {X Y : Scheme.{0}} [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [Mono f]
    (h : Local.GenericLifting.LocalGenericLifting f) : IsClosedImmersion f := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover).mpr
  intro i
  let : IsLocallyNoetherian (Y.affineCover.X i) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)
  let : IsNoetherian (Y.affineCover.X i) := ⟨⟩
  exact (h.baseChange (Y.affineCover.f i)).closedImmersion_of_affine _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
