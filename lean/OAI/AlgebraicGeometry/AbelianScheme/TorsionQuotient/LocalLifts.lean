import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Local Lifts -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts

/-!
# TorsionQuotient: infinitesimal lifts into arbitrary schemes

Maps from the spectrum of a local ring are reconstructed from local maps
out of scheme stalks. Square-zero lifts therefore form a module without
requiring the target scheme to be affine. Postcomposition is induced by
the actual stalk maps of a scheme morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {C : CommRingCat.{u}} [IsLocalRing C]

/-- The actual scheme morphism determined by a local map out of a stalk. -/
noncomputable def ofGerm (X : Scheme.{u}) (x : X) (e : X.presheaf.stalk x ⟶ C) :
    Spec C ⟶ X := Spec.map e ≫ X.fromSpecStalk x

theorem ofGerm_closedPoint (x : X) (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom] :
    ofGerm X x e (IsLocalRing.closedPoint C) = x := by
  change X.fromSpecStalk x (Spec.map e (IsLocalRing.closedPoint C)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem ofGerm_injective (x : X) (e f : X.presheaf.stalk x ⟶ C)
    [IsLocalHom e.hom] [IsLocalHom f.hom]
    (h : ofGerm X x e = ofGerm X x f) : e = f := by
  have hpair := (SpecToEquivOfLocalRing X C).symm.injective
    (show (SpecToEquivOfLocalRing X C).symm ⟨x, ⟨e, inferInstance⟩⟩ =
      (SpecToEquivOfLocalRing X C).symm ⟨x, ⟨f, inferInstance⟩⟩ from h)
  obtain ⟨hx, he⟩ := SpecToEquivOfLocalRing_eq_iff.mp hpair
  simpa using he

omit [IsLocalRing C] in
theorem ofGerm_comp (q : X ⟶ Y) (x : X) (e : X.presheaf.stalk x ⟶ C) :
    ofGerm Y (q x) (q.stalkMap x ≫ e) = ofGerm X x e ≫ q := by
  simp only [ofGerm, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]

variable (J : Ideal C) (hJ : J ^ 2 = ⊥)
variable {x : X} (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom]

/-- The ring-theoretic lift module, with the base map supplied by a stalk. -/
abbrev Lifts := SquareZero.SquareZeroLifts.Lift J hJ e.hom

/-- Realize an infinitesimal stalk lift as a scheme morphism. -/
noncomputable def toPoint (f : Lifts J hJ e) : Spec C ⟶ X :=
  ofGerm X x (CommRingCat.ofHom f.hom)

theorem toPoint_closedPoint (f : Lifts J hJ e) :
    toPoint J hJ e f (IsLocalRing.closedPoint C) = x := by
  let : IsLocalHom (CommRingCat.ofHom f.hom).hom :=
    SquareZero.SquareZeroLifts.isLocalHom_of_congruent J hJ e.hom f.hom f.congruent
  exact ofGerm_closedPoint _ _

omit [IsLocalRing C] [IsLocalHom e.hom] in
@[simp] theorem toPoint_zero : toPoint J hJ e 0 = ofGerm X x e := rfl

theorem toPoint_injective : Function.Injective (toPoint J hJ e) := by
  intro f g h
  let : IsLocalHom (CommRingCat.ofHom f.hom).hom :=
    SquareZero.SquareZeroLifts.isLocalHom_of_congruent J hJ e.hom f.hom f.congruent
  let : IsLocalHom (CommRingCat.ofHom g.hom).hom :=
    SquareZero.SquareZeroLifts.isLocalHom_of_congruent J hJ e.hom g.hom g.congruent
  apply SquareZero.SquareZeroLifts.Lift.ext
  exact congrArg CommRingCat.Hom.hom (ofGerm_injective x
    (CommRingCat.ofHom f.hom) (CommRingCat.ofHom g.hom) h)

omit [IsLocalRing C] [IsLocalHom e.hom] in
theorem toPoint_reduction (f : Lifts J hJ e) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ toPoint J hJ e f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ofGerm X x e := by
  have h : CommRingCat.ofHom f.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      e ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    ext a
    exact Ideal.Quotient.eq.mpr (f.congruent a)
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
      Spec.map (CommRingCat.ofHom f.hom) ≫ X.fromSpecStalk x =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map e ≫ X.fromSpecStalk x
  rw [← Spec.map_comp_assoc (CommRingCat.ofHom f.hom), ← Spec.map_comp_assoc e, h]

/-- Postcomposition of scheme maps induces a linear map on stalk lifts. -/
noncomputable def map (q : X ⟶ Y) : Lifts J hJ e →ₗ[C] Lifts J hJ (q.stalkMap x ≫ e) :=
  SquareZero.SquareZeroLifts.Lift.comap (q.stalkMap x).hom

omit [IsLocalRing C] [IsLocalHom e.hom] in
theorem toPoint_map (q : X ⟶ Y) (f : Lifts J hJ e) :
    toPoint J hJ (q.stalkMap x ≫ e) (LocalSchemeLifts.map J hJ e q f) = toPoint J hJ e f ≫ q :=
  ofGerm_comp q x (CommRingCat.ofHom f.hom)

include hJ in
/-- A square-zero ideal in a nontrivial ring is proper. -/
theorem ideal_ne_top : J ≠ ⊤ := by
  intro htop
  have hone : (1 : C) ∈ J := by simp only [htop, Submodule.mem_top]
  have hz := InfinitesimalEq.Infinitesimal.mul_eq_zero_of_square_zero_ideal J hJ hone hone
  exact one_ne_zero (by simpa only [one_mul] using hz)

/-- Every scheme lift of the prescribed reduction comes from a stalk lift. -/
theorem exists_stalkLift (g : Spec C ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ofGerm X x e) :
    ∃ f : Lifts J hJ e, toPoint J hJ e f = g := by
  let : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (ideal_ne_top J hJ)
  let : IsLocalRing (C ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨⟨y, ⟨v, hv⟩⟩, rfl⟩ := (SpecToEquivOfLocalRing X C).symm.surjective g
  let : IsLocalHom v.hom := hv
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ofGerm X y v =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ofGerm X x e at hg
  have hy : y = x := by
    have hc := congrArg (fun z : Spec (CommRingCat.of (C ⧸ J)) ⟶ X =>
      z (IsLocalRing.closedPoint (C ⧸ J))) hg
    change ofGerm X y v (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (IsLocalRing.closedPoint (C ⧸ J))) =
      ofGerm X x e (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (IsLocalRing.closedPoint (C ⧸ J))) at hc
    have hqcp : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
        (IsLocalRing.closedPoint (C ⧸ J)) = IsLocalRing.closedPoint C :=
      IsLocalRing.comap_closedPoint (Ideal.Quotient.mk J)
    rw [hqcp, ofGerm_closedPoint, ofGerm_closedPoint] at hc
    exact hc
  subst y
  have hmaps : ofGerm X x (v ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      ofGerm X x (e ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    simpa only [ofGerm, Spec.map_comp, Category.assoc] using hg
  let : IsLocalHom (v ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by
    change IsLocalHom ((Ideal.Quotient.mk J).comp v.hom)
    infer_instance
  let : IsLocalHom (e ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by
    change IsLocalHom ((Ideal.Quotient.mk J).comp e.hom)
    infer_instance
  have hring := ofGerm_injective x _ _ hmaps
  refine ⟨⟨v.hom, ?_⟩, rfl⟩
  intro a
  exact Ideal.Quotient.eq.mp (congrArg (fun z => z.hom a) hring)

/-- The intrinsic scheme-theoretic fiber of reduction. -/
abbrev SchemeLifts :=
  { g : Spec C ⟶ X // Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ofGerm X x e }

/-- A module of stalk lifts parametrizes exactly the actual infinitesimal
lifts into an arbitrary scheme; no affine chart on the target is chosen. -/
noncomputable def equivSchemeLifts : Lifts J hJ e ≃ SchemeLifts J e :=
  Equiv.ofBijective (fun f => ⟨toPoint J hJ e f, toPoint_reduction J hJ e f⟩)
    ⟨fun f g h => toPoint_injective J hJ e (congrArg Subtype.val h), by
      rintro ⟨g, hg⟩
      obtain ⟨f, hf⟩ := exists_stalkLift J hJ e g hg
      exact ⟨f, Subtype.ext hf⟩⟩

/-- Relative deformations are the kernel of the linear map on base lifts. -/
noncomputable def relativeModule (q : X ⟶ Y) : Submodule C (Lifts J hJ e) :=
  LinearMap.ker (LocalSchemeLifts.map J hJ e q)

/-- Actual infinitesimal scheme lifts whose morphism to the base stays fixed. -/
abbrev RelativeSchemeLifts (q : X ⟶ Y) :=
  { g : Spec C ⟶ X //
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ofGerm X x e) ∧
      g ≫ q = ofGerm X x e ≫ q }

omit [IsLocalRing C] [IsLocalHom e.hom] in
theorem toPoint_over (q : X ⟶ Y) (f : relativeModule J hJ e q) :
    toPoint J hJ e f.val ≫ q = ofGerm X x e ≫ q := by
  have hf : LocalSchemeLifts.map J hJ e q f.val = 0 := f.property
  rw [← toPoint_map, hf, toPoint_zero, ofGerm_comp]

/-- Intrinsic relative infinitesimal lifts are exactly the points of a
module, even when neither the target scheme nor the base is affine. -/
noncomputable def equivRelativeSchemeLifts (q : X ⟶ Y) :
    relativeModule J hJ e q ≃ RelativeSchemeLifts J e q :=
  Equiv.ofBijective
    (fun f => ⟨toPoint J hJ e f.val,
      toPoint_reduction J hJ e f.val, toPoint_over J hJ e q f⟩)
    ⟨by
      intro f g h
      apply Subtype.ext
      exact toPoint_injective J hJ e (congrArg Subtype.val h), by
      rintro ⟨g, hg, hbase⟩
      obtain ⟨f, hf⟩ := exists_stalkLift J hJ e g hg
      have hlocal : IsLocalHom (q.stalkMap x ≫ e).hom := by
        change IsLocalHom (e.hom.comp (q.stalkMap x).hom)
        infer_instance
      let : IsLocalHom (q.stalkMap x ≫ e).hom := hlocal
      have hker : f ∈ relativeModule J hJ e q := by
        change LocalSchemeLifts.map J hJ e q f = 0
        apply toPoint_injective J hJ (q.stalkMap x ≫ e)
        rw [toPoint_map, toPoint_zero, ofGerm_comp, hf, hbase]
      exact ⟨⟨f, hker⟩, Subtype.ext hf⟩⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts
