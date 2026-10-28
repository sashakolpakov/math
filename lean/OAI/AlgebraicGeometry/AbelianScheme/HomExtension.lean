import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings

/-! # Hom Extension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.HomExtension

/-!
HomExtension: extension of homomorphisms of abelian schemes over a DVR.
The statement's geometric hypotheses are retained without importing its placeholder.
Properness and a codimension-one valuation stalk give an extension on an open
meeting the special fiber. Its difference map is a smooth surjection. Flat
descent constructs the global extension; schematic dominance proves uniqueness
and reflects preservation of the group laws.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

lemma hom_ext_of_schematic_dominance
    {S : Scheme.{u}} {A B : Over S} [IsSeparated B.hom]
    (f g : A ⟶ B) {W : Scheme.{u}} (ι : W ⟶ A.left)
    [IsSchemeTheoreticallyDominant ι]
    (h : ι ≫ f.left = ι ≫ g.left) : f = g := by
  let W' : Over S := Over.mk (ι ≫ A.hom)
  let i : W' ⟶ A := Over.homMk ι
  have hi : i ≫ f = i ≫ g := Over.OverMorphism.ext h
  let l := equalizer.lift i hi
  have hl : l.left ≫ (equalizer.ι f g).left = ι :=
    congrArg Over.Hom.left (equalizer.lift_ι i hi)
  have hk : (equalizer.ι f g).left.ker = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      (equalizer.ι f g).left.ker ≤
          (l.left ≫ (equalizer.ι f g).left).ker :=
        l.left.le_ker_comp _
      _ = ⊥ := by rw [hl, ι.ker_eq_bot]
  have : IsIso (equalizer.ι f g).left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι f g).left]
  exact congrArg Over.Hom.left (equalizer.condition f g)

lemma fraction_field_inclusion_dominant
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap R K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
  exact bot_le

lemma generic_fiber_map_injective
    {R K : Type u}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A B : Over (Spec (CommRingCat.of R)))
    [Flat A.hom] [IsSeparated B.hom] :
    Function.Injective
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
        (X := A) (Y := B)) := by
  let η := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsDominant η := fraction_field_inclusion_dominant
  have : IsSchemeTheoreticallyDominant η :=
    IsSchemeTheoreticallyDominant.of_isDominant η
  intro f g h
  apply hom_ext_of_schematic_dominance f g (pullback.fst A.hom η)
  have h' := congrArg (fun k => k.left ≫ pullback.fst B.hom η) h
  dsimp [Over.pullback, η] at h'
  simpa only [Over.homMk_left, pullback.lift_fst] using h'

open scoped _root_.CategoryTheory.MonObj in
lemma isMonHom_of_generic_fiber
    {R K : Type u}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {A B : Over (Spec (CommRingCat.of R))}
    [GrpObj A] [GrpObj B]
    [Flat A.hom] [IsSeparated B.hom]
    (f : A ⟶ B)
    (hf : IsMonHom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f)) :
    IsMonHom f := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have : IsMonHom (F.map f) := hf
  have : Flat (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
    dsimp
    infer_instance
  have : Flat (A ⊗ A).hom := by
    dsimp
    infer_instance
  constructor
  · apply generic_fiber_map_injective (K := K) (𝟙_ _) B
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    simpa only [Functor.map_comp, Category.assoc, Functor.obj.η_def]
      using (IsMonHom.one_hom (F.map f))
  · apply generic_fiber_map_injective (K := K) (A ⊗ A) B
    apply (cancel_epi (Functor.LaxMonoidal.μ F A A)).mp
    simpa only [Functor.map_comp, Category.assoc, Functor.obj.μ_def,
      Functor.LaxMonoidal.μ_natural_assoc]
      using (IsMonHom.mul_hom (F.map f))

lemma proper_map_extends_near_valuation_stalk
    {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (x : X) [ValuationRing (X.presheaf.stalk x)]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ Y),
      g ≫ sY = U.ι ≫ sX ∧
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        U.fromSpecStalkOfMem x hxU ≫ g = φ := by
  have hw : φ ≫ sY =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [hφ, ← Category.assoc]
    congr 1
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec X).specializes (Set.mem_univ x))).symm
  have : IsDomain (X.presheaf.stalk x) := inferInstance
  let sq : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x
      commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
      domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
      valuationRing := inferInstanceAs (ValuationRing (X.presheaf.stalk x))
      K := X.functionField
      field := inferInstanceAs (Field X.functionField)
      algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) X.functionField)
      isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
      i₁ := φ
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨hw⟩ }
  have H : ValuativeCriterion.Existence sY :=
    ((congrFun (congrFun (congrFun UniversallyClosed.eq_valuativeCriterion Y) S) sY).mp
      (inferInstance : UniversallyClosed sY)).1
  obtain ⟨l, hl₁, hl₂⟩ := (H sq).exists_lift
  obtain ⟨U, hxU, g, hg, hgbase⟩ :=
    spread_out_of_isGermInjective' sX sY (x := x) l hl₂
  refine ⟨U, hxU, g, hgbase, ?_⟩
  rw [← hg]
  exact hl₁

lemma pullback_map_property
    {S T : Scheme.{u}} (e : T ⟶ S) {A B : Over S} (f : A ⟶ B)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hf : P f.left) : P ((Over.pullback e).map f).left := by
  change P (pullback.lift (pullback.fst A.hom e ≫ f.left)
    (pullback.snd A.hom e) _)
  exact P.pullbackLift_fst_snd e f.w.symm hf

/-- A generic morphism which extends on a flat cover descends to the base scheme. -/
lemma descend_generic_map_from_flat_cover
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {A B D : Over (Spec (.of R))}
    [Flat D.hom] [IsSeparated B.hom]
    (p : D ⟶ A) [Flat p.left] [Surjective p.left] [QuasiCompact p.left]
    (fK : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B)
    (g : D ⟶ B)
    (hg : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p ≫ fK =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map g) :
    ∃ f : A ⟶ B,
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f = fK := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let W : Over (Spec (.of R)) := Over.mk (pullback.fst p.left p.left ≫ D.hom)
  change F.map p ≫ fK = F.map g at hg
  let a : W ⟶ D := Over.homMk (pullback.fst p.left p.left)
  let b : W ⟶ D := Over.homMk (pullback.snd p.left p.left) (by
    dsimp [W]
    rw [← p.w, pullback.condition_assoc])
  have hab : a ≫ p = b ≫ p := Over.OverMorphism.ext pullback.condition
  have : Flat W.hom := by dsimp [W]; infer_instance
  have hgg : a ≫ g = b ≫ g := by
    apply generic_fiber_map_injective (K := K) W B
    change F.map (a ≫ g) = F.map (b ≫ g)
    rw [F.map_comp, F.map_comp, ← hg, ← Category.assoc,
      ← Category.assoc, ← F.map_comp, ← F.map_comp, hab]
  have hgg' : pullback.fst p.left p.left ≫ g.left =
      pullback.snd p.left p.left ≫ g.left := congrArg Over.Hom.left hgg
  obtain ⟨f, hf⟩ := IsRegularEpi.exists_of_isKernelPair p.left
    (IsKernelPair.of_hasPullback p.left) g.left hgg'
  have hbase : f ≫ B.hom = A.hom := by
    rw [← cancel_epi p.left, ← Category.assoc, hf, g.w, p.w]
  let f' : A ⟶ B := Over.homMk f hbase
  have hpf : p ≫ f' = g := Over.OverMorphism.ext hf
  have : Flat (F.map p).left := pullback_map_property _ p _ inferInstance
  have : Surjective (F.map p).left := pullback_map_property _ p _ inferInstance
  have : Epi (F.map p).left := Flat.epi_of_flat_of_surjective _
  have : Epi (F.map p) := Over.epi_of_epi_left _
  refine ⟨f', ?_⟩
  change F.map f' = fK
  rw [← cancel_epi (F.map p), ← F.map_comp, hpf]
  exact hg.symm

open scoped _root_.CategoryTheory.MonObj in
open CartesianMonoidalCategory in
lemma extend_hom_from_difference_cover
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {A B U : Over (Spec (.of R))} [GrpObj A] [GrpObj B]
    [Flat A.hom] [Flat U.hom] [IsSeparated B.hom]
    (u : U ⟶ A)
    [Flat ((fst U U ≫ u) / (snd U U ≫ u)).left]
    [Surjective ((fst U U ≫ u) / (snd U U ≫ u)).left]
    [QuasiCompact ((fst U U ≫ u) / (snd U U ≫ u)).left]
    (fK : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B)
    [IsMonHom fK] (g : U ⟶ B)
    (hg : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map u ≫ fK =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map g) :
    ∃! f : A ⟶ B,
      IsMonHom f ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f = fK := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  change F.map u ≫ fK = F.map g at hg
  let d : U ⊗ U ⟶ A := (fst U U ≫ u) / (snd U U ≫ u)
  let h : U ⊗ U ⟶ B := (fst U U ≫ g) / (snd U U ≫ g)
  have : Flat (U ⊗ U).hom := by dsimp; infer_instance
  have hcompat : F.map d ≫ fK = F.map h := by
    dsimp [d, h]
    simp only [div_eq_mul_inv, Functor.map_mul, Functor.map_inv', Functor.map_comp,
      MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hg]
  obtain ⟨f, hf⟩ := descend_generic_map_from_flat_cover d fK h hcompat
  refine ⟨f, ⟨?_, hf⟩, ?_⟩
  · apply isMonHom_of_generic_fiber (K := K) f
    rw [hf]
    infer_instance
  · intro f' hf'
    exact generic_fiber_map_injective (K := K) A B (hf'.2.trans hf.symm)

open scoped _root_.CategoryTheory.MonObj in
open CartesianMonoidalCategory in
noncomputable def differenceShear {S : Scheme.{u}} (A : Over S) [GrpObj A] :
    A ⊗ A ≅ A ⊗ A where
  hom := lift (fst A A / snd A A) (snd A A)
  inv := lift (fst A A * snd A A) (snd A A)
  hom_inv_id := by
    apply hom_ext <;> simp [MonObj.comp_mul]
  inv_hom_id := by
    apply hom_ext <;> simp [GrpObj.comp_div]

open scoped _root_.CategoryTheory.MonObj in
open CartesianMonoidalCategory in
lemma smooth_difference_of_open_immersion
    {S : Scheme.{u}} {A U : Over S} [GrpObj A] [Smooth A.hom]
    (u : U ⟶ A) [IsOpenImmersion u.left] :
    Smooth ((fst U U ≫ u) / (snd U U ≫ u)).left := by
  have : Smooth (fst A A).left := by dsimp; infer_instance
  have : IsOpenImmersion (u ⊗ₘ u).left := by
    change IsOpenImmersion (pullback.map U.hom U.hom A.hom A.hom
      u.left u.left (𝟙 S) (by simp) (by simp))
    infer_instance
  have : IsIso (differenceShear A).hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map (differenceShear A).hom))
  have h : (u ⊗ₘ u) ≫ (differenceShear A).hom ≫ fst A A =
      (fst U U ≫ u) / (snd U U ≫ u) := by
    simp [differenceShear, GrpObj.comp_div]
  rw [← h]
  change Smooth ((u ⊗ₘ u).left ≫ (differenceShear A).hom.left ≫ (fst A A).left)
  infer_instance

lemma lift_field_point_to_open
    {k : Type u} [Field k] {A U : Over (Spec (.of k))}
    (u : U ⟶ A) [IsOpenImmersion u.left]
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A)
    (ha : a.left (IsLocalRing.closedPoint k) ∈ Set.range u.left) :
    ∃ l : 𝟙_ (Over (Spec (.of k))) ⟶ U, l ≫ u = a := by
  have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have hrange : Set.range a.left ⊆ Set.range u.left := by
    rintro _ ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    simpa only [ht] using ha
  let l := IsOpenImmersion.lift u.left a.left hrange
  have hl : l ≫ u.left = a.left := IsOpenImmersion.lift_fac _ _ _
  have hb : l ≫ U.hom = (𝟙_ (Over (Spec (.of k)))).hom := by
    rw [← u.w, ← Category.assoc, hl, a.w]
  exact ⟨Over.homMk l hb, Over.OverMorphism.ext hl⟩

open scoped _root_.CategoryTheory.MonObj in
open CartesianMonoidalCategory in
lemma difference_surjective_over_algebraically_closed_field
    {k : Type u} [Field k] [IsAlgClosed k]
    {A U : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IrreducibleSpace A.left] [Nonempty U.left]
    (u : U ⟶ A) [IsOpenImmersion u.left] :
    Surjective ((fst U U ≫ u) / (snd U U ≫ u)).left := by
  let d : U ⊗ U ⟶ A := (fst U U ≫ u) / (snd U U ≫ u)
  have : Smooth d.left := smooth_difference_of_open_immersion u
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  constructor
  intro x
  by_contra hx
  have hn : ((Set.range d.left)ᶜ).Nonempty := ⟨x, hx⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hn
    d.left.isOpenMap.isOpen_range.isClosed_compl.isLocallyClosed
  let z' : 𝟙_ (Over (Spec (.of k))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom z hzc) (pointOfClosedPoint_comp A.hom z hzc)
  let α := GrpObj.mulRight z'
  have : IsIso α.hom.left := inferInstanceAs
    (IsIso ((Over.forget (Spec (.of k))).map α.hom))
  let V := u.left.opensRange
  have hV : (V : Set A.left).Nonempty := Set.range_nonempty u.left
  have hαV : (α.hom.left ⁻¹ᵁ V : Set A.left).Nonempty :=
    hV.preimage α.hom.left.surjective
  have hT : ((V ⊓ α.hom.left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty := by
    simpa only [TopologicalSpace.Opens.coe_inf, Set.inter_comm] using
      (V.isOpen.dense hV).inter_open_nonempty _ (α.hom.left ⁻¹ᵁ V).isOpen hαV
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints hT
    (V ⊓ α.hom.left ⁻¹ᵁ V).isOpen.isLocallyClosed
  let b' : 𝟙_ (Over (Spec (.of k))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom b hbc) (pointOfClosedPoint_comp A.hom b hbc)
  have hbpoint : b'.left (IsLocalRing.closedPoint k) = b :=
    pointOfClosedPoint_apply A.hom b hbc _
  obtain ⟨lb, hlb⟩ := lift_field_point_to_open u b' (by
    rw [hbpoint]
    exact hb.1)
  obtain ⟨la, hla⟩ := lift_field_point_to_open u (b' ≫ α.hom) (by
    change α.hom.left (b'.left (IsLocalRing.closedPoint k)) ∈ Set.range u.left
    rw [hbpoint]
    exact hb.2)
  have htrans : b' ≫ α.hom = b' * z' := by
    dsimp [α, GrpObj.mulRight]
    rw [Hom.mul_def, ← Category.assoc, comp_lift]
    simp
  let q := lift la lb
  have hq : q ≫ d = z' := by
    simp [q, d, GrpObj.comp_div, hla, hlb, htrans]
  apply hz
  refine ⟨q.left (IsLocalRing.closedPoint k), ?_⟩
  calc
    d.left (q.left (IsLocalRing.closedPoint k)) =
        (q ≫ d).left (IsLocalRing.closedPoint k) := rfl
    _ = z'.left (IsLocalRing.closedPoint k) := congrArg
      (fun f => f.left (IsLocalRing.closedPoint k)) hq
    _ = z := pointOfClosedPoint_apply A.hom z hzc _

open scoped _root_.CategoryTheory.MonObj in
open CartesianMonoidalCategory in
lemma pullback_difference
    {S T : Scheme.{u}} (e : T ⟶ S) {A U : Over S} [GrpObj A] (u : U ⟶ A) :
    Functor.LaxMonoidal.μ (Over.pullback e) U U ≫
      (Over.pullback e).map ((fst U U ≫ u) / (snd U U ≫ u)) =
      (fst ((Over.pullback e).obj U) ((Over.pullback e).obj U) ≫
        (Over.pullback e).map u) /
      (snd ((Over.pullback e).obj U) ((Over.pullback e).obj U) ≫
        (Over.pullback e).map u) := by
  simp only [div_eq_mul_inv, Functor.map_mul, Functor.map_inv', Functor.map_comp,
    MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd]

lemma pullback_map_fst
    {S T : Scheme.{u}} (e : T ⟶ S) {A B : Over S} (f : A ⟶ B) :
    ((Over.pullback e).map f).left ≫ pullback.fst B.hom e =
      pullback.fst A.hom e ≫ f.left := by
  change pullback.lift _ _ _ ≫ pullback.fst B.hom e = _
  exact pullback.lift_fst _ _ _

open scoped _root_.CategoryTheory.MonObj in
open CartesianMonoidalCategory in
lemma difference_surjective_of_geometrically_irreducible
    {S : Scheme.{u}} {A U : Over S} [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [GeometricallyIrreducible A.hom] [Surjective U.hom]
    (u : U ⟶ A) [IsOpenImmersion u.left] :
    Surjective ((fst U U ≫ u) / (snd U U ≫ u)).left := by
  let d : U ⊗ U ⟶ A := (fst U U ≫ u) / (snd U U ≫ u)
  constructor
  intro x
  let Ω := AlgebraicClosure (A.left.residueField x)
  let qx : Spec (.of Ω) ⟶ A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField x) Ω)) ≫
      A.left.fromSpecResidueField x
  let e := qx ≫ A.hom
  let F := Over.pullback e
  have : Smooth (F.obj A).hom := by dsimp [F]; infer_instance
  have : IrreducibleSpace (F.obj A).left :=
    GeometricallyIrreducible.geometrically_irreducibleSpace e _ _
      (IsPullback.of_hasPullback A.hom e)
  have : Nonempty (F.obj U).left :=
    ⟨((pullback.snd U.hom e).surjective (IsLocalRing.closedPoint Ω)).choose⟩
  have : IsOpenImmersion (F.map u).left := pullback_map_property e u _ inferInstance
  have hd := difference_surjective_over_algebraically_closed_field (F.map u)
  have hcomp : Surjective ((Functor.LaxMonoidal.μ F U U).left ≫ (F.map d).left) := by
    change Surjective (Functor.LaxMonoidal.μ F U U ≫ F.map d).left
    rw [show Functor.LaxMonoidal.μ F U U ≫ F.map d = _ from pullback_difference e u]
    exact hd
  have : Surjective (F.map d).left :=
    Surjective.of_comp (Functor.LaxMonoidal.μ F U U).left (F.map d).left
  let a : Spec (.of Ω) ⟶ (F.obj A).left := pullback.lift qx (𝟙 _) (by simp [e])
  obtain ⟨y, hy⟩ := (F.map d).left.surjective (a (IsLocalRing.closedPoint Ω))
  refine ⟨(pullback.fst (U ⊗ U).hom e) y, ?_⟩
  change d.left ((pullback.fst (U ⊗ U).hom e) y) = x
  calc
    d.left ((pullback.fst (U ⊗ U).hom e) y) =
        (pullback.fst A.hom e) ((F.map d).left y) :=
      congrArg (fun f => f y) (pullback_map_fst e d).symm
    _ = (pullback.fst A.hom e) (a (IsLocalRing.closedPoint Ω)) := by rw [hy]
    _ = x := by
      change (a ≫ pullback.fst A.hom e) (IsLocalRing.closedPoint Ω) = x
      have ha : a ≫ pullback.fst A.hom e = qx := pullback.lift_fst _ _ _
      rw [ha]
      change A.left.fromSpecResidueField x _ = x
      exact A.left.fromSpecResidueField_apply x _

lemma generic_point_map_dominant (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro x
  apply (genericPoint_specializes x).mem_closed isClosed_closure
  apply subset_closure
  exact ⟨IsLocalRing.closedPoint X.functionField, X.fromSpecStalk_closedPoint⟩

lemma generic_point_lifts_to_generic_fiber
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A : Over (Spec (.of R))) [Flat A.hom] [IsIntegral A.left] :
    ∃ l : Spec A.left.functionField ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).left,
      l ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        A.left.fromSpecStalk (genericPoint A.left) := by
  let e := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion e := HomExtensionLocalRings.LocalRings.fraction_inclusion_isOpenImmersion
  have : IsDominant e := fraction_field_inclusion_dominant
  have : IsSchemeTheoreticallyDominant e := IsSchemeTheoreticallyDominant.of_isDominant e
  let j := pullback.fst A.hom e
  let t := Classical.choice j.denseRange.nonempty
  have hj : genericPoint A.left ∈ j.opensRange :=
    (genericPoint_specializes (j t)).mem_open j.opensRange.isOpen ⟨t, rfl⟩
  have : Subsingleton (Spec (A.left.presheaf.stalk (genericPoint A.left))) :=
    inferInstanceAs (Subsingleton (Spec (.of A.left.functionField)))
  have hr : Set.range (A.left.fromSpecStalk (genericPoint A.left)) ⊆ Set.range j := by
    rintro _ ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint A.left.functionField := Subsingleton.elim _ _
    rw [ht, A.left.fromSpecStalk_closedPoint]
    exact hj
  exact ⟨IsOpenImmersion.lift j _ hr, IsOpenImmersion.lift_fac _ _ _⟩

lemma exists_open_extension_over_dvr
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A B : Over (Spec (.of R))) [Smooth A.hom] [Surjective A.hom]
    [IsIntegral A.left] [AlgebraicGeometry.IsNoetherian A.left] [IsProper B.hom]
    (fK : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B) :
    ∃ V : A.left.Opens,
      let U : Over (Spec (.of R)) := Over.mk (V.ι ≫ A.hom)
      let u : U ⟶ A := Over.homMk V.ι
      ∃ g : U ⟶ B, Surjective U.hom ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map u ≫ fK =
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map g := by
  let e := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F := Over.pullback e
  have : IsOpenImmersion e := HomExtensionLocalRings.LocalRings.fraction_inclusion_isOpenImmersion
  obtain ⟨x, hxbase, hxcodim⟩ := HomExtensionLocalRings.LocalRings.exists_codimension_one_in_special_fiber A.hom
  have : IsDiscreteValuationRing (A.left.presheaf.stalk x) :=
    HomExtensionLocalRings.LocalRings.smooth_stalk_isDiscreteValuationRing A.hom x hxcodim
  obtain ⟨l, hl⟩ := generic_point_lifts_to_generic_fiber (K := K) A
  have hfK : fK.left ≫ pullback.snd B.hom e = pullback.snd A.hom e := fK.w
  let φ := l ≫ fK.left ≫ pullback.fst B.hom e
  have hφ : φ ≫ B.hom = A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom := by
    calc
      φ ≫ B.hom = l ≫ fK.left ≫ pullback.snd B.hom e ≫ e := by
        dsimp [φ]
        rw [Category.assoc, Category.assoc, pullback.condition]
      _ = l ≫ pullback.snd A.hom e ≫ e := by
        rw [← Category.assoc fK.left, hfK]
      _ = l ≫ pullback.fst A.hom e ≫ A.hom := by rw [pullback.condition]
      _ = A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom := by
        rw [← Category.assoc, hl]
  obtain ⟨V, hxV, g, hgbase, hφg⟩ :=
    proper_map_extends_near_valuation_stalk A.hom B.hom x φ hφ
  let U : Over (Spec (.of R)) := Over.mk (V.ι ≫ A.hom)
  let u : U ⟶ A := Over.homMk V.ι
  let g' : U ⟶ B := Over.homMk g hgbase
  have : Smooth U.hom := by dsimp [U]; infer_instance
  have hsurj : Surjective U.hom := by
    constructor
    intro s
    exact (IsLocalRing.specializes_closedPoint s).mem_open U.hom.isOpenMap.isOpen_range
      (show IsLocalRing.closedPoint R ∈ Set.range U.hom from ⟨⟨x, hxV⟩, hxbase⟩)
  refine ⟨V, g', hsurj, ?_⟩
  change F.map u ≫ fK = F.map g'
  let aV := Spec.map (CommRingCat.ofHom
    (algebraMap (A.left.presheaf.stalk x) A.left.functionField)) ≫
    V.fromSpecStalkOfMem x hxV
  have haV : aV ≫ V.ι = A.left.fromSpecStalk (genericPoint A.left) := by
    dsimp [aV]
    rw [Category.assoc, V.fromSpecStalkOfMem_ι]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec A.left).specializes (Set.mem_univ x))
  let aK : Spec A.left.functionField ⟶ (F.obj U).left :=
    pullback.lift aV (l ≫ pullback.snd A.hom e) (by
      change aV ≫ V.ι ≫ A.hom = (l ≫ pullback.snd A.hom e) ≫ e
      rw [← Category.assoc aV, haV, ← hl, Category.assoc, pullback.condition,
        Category.assoc])
  have haK : aK ≫ pullback.fst U.hom e = aV := pullback.lift_fst _ _ _
  have hau : aK ≫ (F.map u).left = l := by
    rw [← cancel_mono (pullback.fst A.hom e), Category.assoc,
      pullback_map_fst e u, ← Category.assoc, haK]
    exact haV.trans hl.symm
  let j := pullback.fst U.hom e ≫ V.ι
  have haj : aK ≫ j = A.left.fromSpecStalk (genericPoint A.left) := by
    rw [← Category.assoc, haK]
    exact haV
  have : IsDominant (aK ≫ j) := haj.symm ▸ generic_point_map_dominant A.left
  have : IsDominant aK := IsDominant.of_comp_of_isOpenImmersion aK j
  have : IsReduced (F.obj U).left := isReduced_of_isOpenImmersion j
  have hbase (q : F.obj U ⟶ F.obj B) :
      (q.left ≫ pullback.fst B.hom e) ≫ B.hom = (F.obj U).hom ≫ e := by
    have hq : q.left ≫ pullback.snd B.hom e = (F.obj U).hom := q.w
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq]
  apply Over.OverMorphism.ext
  apply (cancel_mono (pullback.fst B.hom e)).mp
  apply ext_of_isDominant_of_isSeparated B.hom
    ((hbase (F.map u ≫ fK)).trans (hbase (F.map g')).symm) aK
  calc
    aK ≫ ((F.map u ≫ fK).left ≫ pullback.fst B.hom e) = φ := by
      change aK ≫ ((F.map u).left ≫ fK.left) ≫ pullback.fst B.hom e = φ
      rw [← Category.assoc aK, ← Category.assoc aK, hau]
      rfl
    _ = aV ≫ g := hφg.symm
    _ = aK ≫ ((F.map g').left ≫ pullback.fst B.hom e) := by
      rw [pullback_map_fst e g', ← Category.assoc, haK]
      rfl

theorem neron_extension_of_abelian_hom
    {R K : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A B : Over (Spec (CommRingCat.of R)))
    [GrpObj A] [IsCommMonObj A]
    [GrpObj B] [IsCommMonObj B]
    [IsProper A.hom] [Smooth A.hom]
    [GeometricallyConnected A.hom]
    [IsProper B.hom] [Smooth B.hom]
    [GeometricallyConnected B.hom] :
    let η := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let genericFiber := Over.pullback η
    ∀ fK : genericFiber.obj A ⟶ genericFiber.obj B,
      IsMonHom fK →
        ∃! f : A ⟶ B,
          IsMonHom f ∧ genericFiber.map f = fK := by
  dsimp only
  intro fK hfK
  have : IsMonHom fK := hfK
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : AlgebraicGeometry.IsNoetherian A.left := {}
  have : IsIntegral A.left := HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected A.hom
  have : GeometricallyIrreducible A.hom :=
    HomExtensionLocalRings.LocalRings.geometricallyIrreducible_of_smooth_proper_connected A.hom
  obtain ⟨V, g, hsurj, hg⟩ := exists_open_extension_over_dvr A B fK
  let U : Over (Spec (.of R)) := Over.mk (V.ι ≫ A.hom)
  let u : U ⟶ A := Over.homMk V.ι
  have : IsOpenImmersion u.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : Smooth U.hom := by dsimp [U]; infer_instance
  have : Surjective U.hom := hsurj
  have : TopologicalSpace.NoetherianSpace U.left :=
    u.left.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace U.left := TopologicalSpace.NoetherianSpace.compactSpace U.left
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : AlgebraicGeometry.IsNoetherian U.left := {}
  have : Smooth (U ⊗ U).hom := by dsimp; infer_instance
  have : CompactSpace (U ⊗ U).left := by dsimp; infer_instance
  have : IsLocallyNoetherian (U ⊗ U).left :=
    LocallyOfFiniteType.isLocallyNoetherian (U ⊗ U).hom
  have : AlgebraicGeometry.IsNoetherian (U ⊗ U).left := {}
  have := smooth_difference_of_open_immersion u
  have := difference_surjective_of_geometrically_irreducible u
  exact extend_hom_from_difference_cover u fK g hg

end OAI.AlgebraicGeometry.AbelianScheme.HomExtension
