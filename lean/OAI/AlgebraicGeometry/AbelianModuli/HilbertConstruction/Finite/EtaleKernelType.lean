import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FieldMarkingsOf
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleIff
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleGroupPointCount
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic

/-! # Etale Kernel Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.EtaleKernelType.FiniteEtaleKernelType

noncomputable section

/-! Exact geometric group type and scheme-theoretic degree cut out a
clopen locus for an actual finite étale commutative group. Factorization
through the locus is characterized on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

local instance kernelType_unit_finite {S : Scheme.{u}} :
    IsFinite (𝟙_ (Over S)).hom := by
  change IsFinite (𝟙 S)
  infer_instance

local instance kernelType_unit_etale {S : Scheme.{u}} :
    Etale (𝟙_ (Over S)).hom := by
  change Etale (𝟙 S)
  infer_instance

variable {S : Scheme.{u}} (H : Over S) [GrpObj H] [IsCommMonObj H]
  [IsFinite H.hom] [Etale H.hom]

theorem geometricPoints_card (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    Nat.card (Over.mk s ⟶ H) = H.hom.finrank (s (IsLocalRing.closedPoint K)) := by
  let : GrpObj ((Over.pullback s).obj H) := Functor.grpObjObj (F := Over.pullback s)
  let : IsCommMonObj ((Over.pullback s).obj H) :=
    Functor.isCommMonObj_obj (F := Over.pullback s) (M := H)
  have : IsFinite ((Over.pullback s).obj H).hom :=
    inferInstanceAs (IsFinite (pullback.snd H.hom s))
  have : Etale ((Over.pullback s).obj H).hom :=
    inferInstanceAs (Etale (pullback.snd H.hom s))
  let e : (Over.map s).obj (𝟙_ (Over (Spec (CommRingCat.of K)))) ≅ Over.mk s :=
    Over.isoMk (Iso.refl _) (by simp)
  let q : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ (Over.pullback s).obj H) ≃
      (Over.mk s ⟶ H) :=
    ((Over.mapPullbackAdj s).homEquiv _ H).symm.trans (e.homCongr (Iso.refl H))
  calc
    Nat.card (Over.mk s ⟶ H) =
        Nat.card (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ (Over.pullback s).obj H) :=
      (Nat.card_congr q).symm
    _ = ((Over.pullback s).obj H).hom.finrank (IsLocalRing.closedPoint K) :=
      FormalGeometry.Completion.Finite.EtaleGroupPointCount.Construction.finiteEtaleGroup_card_points_eq_finrank
        (Grp.mk ((Over.pullback s).obj H)) _
    _ = _ := Scheme.Hom.finrank_pullback_snd H.hom s _

variable (M : Type u) [Group M] [Fintype M]

def degreeOpen (r : ℕ) : S.Opens :=
  ⟨{s | H.hom.finrank s = r}, H.hom.isLocallyConstant_finrank.isOpen_fiber r⟩

def embeddingImage : S.Opens :=
  AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage.locus (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M))

omit [IsCommMonObj H] in
theorem embeddingImage_isClopen : IsClopen (embeddingImage H M : Set S) :=
  ⟨AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage.locus_closed (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M)),
    (embeddingImage H M).isOpen⟩

def locus (r : ℕ) : S.Opens := degreeOpen H r ⊓ embeddingImage H M

omit [IsCommMonObj H] in
theorem locus_isClopen (r : ℕ) : IsClopen (locus H M r : Set S) :=
  H.hom.isLocallyConstant_finrank.isClopen_fiber r |>.inter (embeddingImage_isClopen H M)

omit [IsCommMonObj H] in
theorem range_embeddingImage_iff (T : Over S) :
    Set.range T.hom ⊆ (embeddingImage H M : Set S) ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S) (_x : Over.mk s ⟶ T),
        Nonempty (Over.mk s ⟶ AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M) := by
  change Set.range (toUnit T).left ⊆
    Set.range (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M)).left ↔ _
  refine (AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage.factors_iff_range
    (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M)) (toUnit T)).symm.trans ?_
  refine (AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage.factors_iff_geometric
    (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M)) (toUnit T)).trans ?_
  constructor
  · intro h K hK hclosed s x
    obtain ⟨z, _⟩ := (AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage.geometric_factors_iff
      (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M)) K s (x ≫ toUnit T)).mp (h K s x)
    exact ⟨z⟩
  · intro h K hK hclosed s x
    apply (AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage.geometric_factors_iff
      (toUnit (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M)) K s (x ≫ toUnit T)).mpr
    obtain ⟨z⟩ := h K s x
    exact ⟨z, Subsingleton.elim _ _⟩

theorem range_locus_iff (r : ℕ) (hr : Nat.card M = r) (T : Over S) :
    Set.range T.hom ⊆ (locus H M r : Set S) ↔
      (∀ t : T.left, H.hom.finrank (T.hom t) = r) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ T.left),
        Nonempty ((Over.mk (p ≫ T.hom) ⟶ H) ≃* M) := by
  constructor
  · intro h
    have hd (t : T.left) : H.hom.finrank (T.hom t) = r := (h ⟨t, rfl⟩).1
    have hi : Set.range T.hom ⊆ (embeddingImage H M : Set S) := fun _ ht => (h ht).2
    refine ⟨hd, ?_⟩
    intro K hK hclosed p
    let s := p ≫ T.hom
    let x : Over.mk s ⟶ T := Over.homMk p rfl
    obtain ⟨z⟩ := (range_embeddingImage_iff H M T).mp hi K s x
    let a := AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.points H M (Over.mk s) z
    have ha : Function.Injective a.val := by
      simpa only [Category.id_comp] using a.property K s (𝟙 (Over.mk s))
    have hs : H.hom.finrank (s (IsLocalRing.closedPoint K)) = r := by
      change H.hom.finrank (T.hom (p (IsLocalRing.closedPoint K))) = r
      exact hd _
    have hc : Nat.card (Over.mk s ⟶ H) = Nat.card M :=
      (geometricPoints_card H K s).trans (hs.trans hr.symm)
    have : Finite (Over.mk s ⟶ H) :=
      Nat.finite_of_card_ne_zero (hc.trans_ne (Nat.card_pos (α := M)).ne')
    exact ⟨(MulEquiv.ofBijective a.val (ha.bijective_of_nat_card_le hc.le)).symm⟩
  · rintro ⟨hd, hg⟩
    have hi : Set.range T.hom ⊆ (embeddingImage H M : Set S) :=
      (range_embeddingImage_iff H M T).mpr (by
        intro K hK hclosed s x
        obtain ⟨e⟩ : Nonempty ((Over.mk s ⟶ H) ≃* M) := by
          have hx : x.left ≫ T.hom = s := x.w
          exact (congrArg (fun b : Spec (CommRingCat.of K) ⟶ S =>
            Nonempty ((Over.mk b ⟶ H) ≃* M)) hx).mp (hg K x.left)
        exact ⟨AbelianScheme.TorsionQuotient.FieldMarkingsOf.FieldMarkings.ofInjective K s e.symm.toMonoidHom e.symm.injective⟩)
    rintro _ ⟨t, rfl⟩
    exact ⟨hd t, hi ⟨t, rfl⟩⟩

theorem factors_locus_iff (r : ℕ) (hr : Nat.card M = r) (T : Scheme.{u}) (a : T ⟶ S) :
    (∃ b : T ⟶ (locus H M r : S.Opens), b ≫ (locus H M r).ι = a) ↔
      (∀ t : T, H.hom.finrank (a t) = r) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ T),
        Nonempty ((Over.mk (p ≫ a) ⟶ H) ≃* M) := by
  have hf :
      (∃ b : T ⟶ (locus H M r : S.Opens), b ≫ (locus H M r).ι = a) ↔
        Set.range a ⊆ (locus H M r : Set S) := by
    constructor
    · rintro ⟨b, rfl⟩ _ ⟨t, rfl⟩
      exact (b t).property
    · intro ha
      have ha' : Set.range a ⊆ Set.range (locus H M r).ι := by
        rwa [Scheme.Opens.range_ι]
      exact ⟨IsOpenImmersion.lift (locus H M r).ι a ha', IsOpenImmersion.lift_fac _ _ _⟩
  exact hf.trans (range_locus_iff H M r hr (Over.mk a))

theorem exists_polarizationTypeOpen {g : ℕ} (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i) :
    ∃ U : S.Opens, IsClopen (U : Set S) ∧
      ∀ (T : Scheme.{u}) (a : T ⟶ S),
        (∃ b : T ⟶ U, b ≫ U.ι = a) ↔
          (∀ t : T, H.hom.finrank (a t) = (∏ i, δ i) ^ 2) ∧
          ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ T),
            Nonempty ((Over.mk (p ≫ a) ⟶ H) ≃*
              Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) := by
  classical
  let (i : Fin g) : NeZero (δ i) := ⟨(hδ i).ne'⟩
  let G := Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))
  let M : Type u := ULift.{u} G
  have hr : Nat.card M = (∏ i, δ i) ^ 2 := by
    simp [M, G, Nat.card_eq_fintype_card, Fintype.card_pi, sq]
  refine ⟨locus H M ((∏ i, δ i) ^ 2), locus_isClopen H M ((∏ i, δ i) ^ 2), ?_⟩
  intro T a
  refine (factors_locus_iff H M ((∏ i, δ i) ^ 2) hr T a).trans ?_
  constructor
  · rintro ⟨hd, hg⟩
    refine ⟨hd, ?_⟩
    intro K hK hclosed p
    obtain ⟨e⟩ := hg K p
    exact ⟨e.trans (MulEquiv.ulift : M ≃* G)⟩
  · rintro ⟨hd, hg⟩
    refine ⟨hd, ?_⟩
    intro K hK hclosed p
    obtain ⟨e⟩ := hg K p
    exact ⟨e.trans (MulEquiv.ulift : M ≃* G).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.EtaleKernelType.FiniteEtaleKernelType
