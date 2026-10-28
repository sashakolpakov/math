import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductPoints

/-! # CM Points Splitting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction

noncomputable section

section

/-!
The split coefficient idempotents decompose actual torsion points into
the native CMPoints blocks on every test scheme. Their sum and orthogonality
are proved modulo q^n, using the actual integral action.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ} {O : Type} [CommRing O]

theorem integralAction_finset_sum (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) {I : Type*} (s : Finset I) (f : I → O) :
    ρ.map (∑ v ∈ s, f v) = ∏ v ∈ s, ρ.map (f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty] using ρ.map_zero
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ρ.map_add, ih]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n : ℕ)

local instance : Fintype Gal(E/ℚ) := Fintype.ofFinite _
local instance : DecidableEq Gal(E/ℚ) := Classical.decEq _

theorem l45Projector_idempotent_congruent (τ : Gal(E/ℚ)) :
    (j.projector iota hsplit n τ) * (j.projector iota hsplit n τ) - j.projector iota hsplit n τ ∈
      Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)) := by
  classical
  rw [← (hsplit n).2]
  change j.residueCoordinates iota n (_ * _ - _) = 0
  rw [map_sub, map_mul, j.projector_coordinates iota hsplit n τ]
  ext υ
  by_cases h : υ = τ
  · subst υ
    simp
  · simp [h]

theorem l45Projectors_sum_congruent :
    (∑ τ : Gal(E/ℚ), j.projector iota hsplit n τ) - 1 ∈
      Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)) := by
  classical
  rw [← (hsplit n).2]
  change j.residueCoordinates iota n (_ - 1) = 0
  rw [map_sub, map_one]
  apply sub_eq_zero.mpr
  rw [map_sum]
  ext υ
  simp [j.projector_coordinates iota hsplit n]

def l45ProjectorPoint (T : Over S) (x : A.torsionPoints (q ^ n) T) (τ : Gal(E/ℚ)) :
    PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T := by
  let e := j.projector iota hsplit n τ
  refine ⟨x.val ≫ ρ.map e, (PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A ρ n τ T _).mpr ⟨?_, ?_⟩⟩
  · exact (MonObj.pow_comp x.val (q ^ n) (ρ.map e)).symm.trans
      ((congrArg (fun f => f ≫ ρ.map e) x.property).trans (MonObj.one_comp _))
  · have h := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A ρ (e * e) e (q ^ n)
      (by simpa only [Nat.cast_pow] using l45Projector_idempotent_congruent j iota hsplit n τ)
      T x.val x.property
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => x.val ≫ f) (ρ.map_mul e e).symm).trans h)

theorem l45Projector_on_block (T : Over S) (τ υ : Gal(E/ℚ))
    (x : PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota υ) n T) :
    x.val ≫ ρ.map (j.projector iota hsplit n τ) = if υ = τ then x.val else 1 := by
  classical
  by_cases h : υ = τ
  · subst υ
    rw [ite_eq_left rfl]
    exact ((PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A ρ n τ T x.val).mp x.property).2
  · rw [ite_eq_right h, x.property.2]
    have hc := congrFun (j.projector_coordinates iota hsplit n τ) υ
    have hz : PadicInt.toZModPow n (j.localCharacter iota υ (j.projector iota hsplit n τ)) = 0 := by
      exact hc.trans (Pi.single_eq_of_ne h _)
    rw [hz, ZMod.val_zero, pow_zero]

theorem l45ProjectorPoint_product (T : Over S) (x : A.torsionPoints (q ^ n) T) :
    (∏ τ : Gal(E/ℚ), (l45ProjectorPoint j iota hsplit A ρ n T x τ).val) = x.val := by
  let pre : (A.scheme ⟶ A.scheme) →* (T ⟶ A.scheme) :=
    ((yonedaGrp.obj (Grp.mk A.scheme)).map x.val.op).hom
  let z := ∑ τ : Gal(E/ℚ), j.projector iota hsplit n τ
  have hz : z - 1 ∈ Ideal.span ({((q ^ n : ℕ) : NumberField.RingOfIntegers E)} :
      Set (NumberField.RingOfIntegers E)) := by
    simpa only [Nat.cast_pow] using l45Projectors_sum_congruent j iota hsplit n
  have hcong := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A ρ z 1 (q ^ n) hz T x.val x.property
  calc
    (∏ τ : Gal(E/ℚ), x.val ≫ ρ.map (j.projector iota hsplit n τ)) =
        x.val ≫ ∏ τ : Gal(E/ℚ), ρ.map (j.projector iota hsplit n τ) :=
      (map_prod pre _ _).symm
    _ = x.val ≫ ρ.map (∑ τ : Gal(E/ℚ), j.projector iota hsplit n τ) :=
      congrArg (fun f => x.val ≫ f) (integralAction_finset_sum A ρ _ _).symm
    _ = x.val ≫ ρ.map 1 := hcong
    _ = x.val := by rw [ρ.map_one, Category.comp_id]

/-- The complete block decomposition, with every infinitesimal point
and its actual group law preserved. -/
def l45TorsionPointsEquivBlocks (T : Over S) :
    A.torsionPoints (q ^ n) T ≃* (∀ τ : Gal(E/ℚ), PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) where
  toFun x := l45ProjectorPoint j iota hsplit A ρ n T x
  invFun x := ⟨∏ τ, (x τ).val, by
    exact (map_prod (powMonoidHom (q ^ n)) _ _).trans
      (Finset.prod_eq_one (fun τ _ => (x τ).property.1))⟩
  left_inv x := Subtype.ext (l45ProjectorPoint_product j iota hsplit A ρ n T x)
  right_inv x := by
    classical
    funext τ
    apply Subtype.ext
    change (∏ υ, (x υ).val) ≫ ρ.map (j.projector iota hsplit n τ) = (x τ).val
    calc
      _ = ∏ υ, (x υ).val ≫ ρ.map (j.projector iota hsplit n τ) :=
        map_prod (IsMonHom.monoidHom (ρ.map (j.projector iota hsplit n τ)) T) _ _
      _ = ∏ υ, if υ = τ then (x υ).val else 1 := by
        apply Finset.prod_congr rfl
        intro υ _
        exact l45Projector_on_block j iota hsplit A ρ n T τ υ (x υ)
      _ = (x τ).val := by simp
  map_mul' x y := by
    funext τ
    apply Subtype.ext
    exact MonObj.mul_comp x.val y.val (ρ.map (j.projector iota hsplit n τ))

theorem l45TorsionPointsEquivBlocks_natural {T U : Over S} (f : T ⟶ U)
    (x : A.torsionPoints (q ^ n) U) (τ : Gal(E/ℚ)) :
    l45TorsionPointsEquivBlocks j iota hsplit A ρ n T (A.torsionPullback (q ^ n) f x) τ =
      PELModuli.CMPoints.BlocksProjectors.blockPullback A ρ (j.localCharacter iota τ) n f
        (l45TorsionPointsEquivBlocks j iota hsplit A ρ n U x τ) :=
  Subtype.ext (Category.assoc f x.val (ρ.map (j.projector iota hsplit n τ)))

end

section

/-!
The actual torsion scheme is identified with the product of its native
chosen/opposite blocks. This is constructed from the coefficient
projectors, not assumed as an additional geometric compatibility.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n r : ℕ) (labels : (Fin r × Bool) ≃ Gal(E/ℚ))

abbrev l45PairedBlockFamily (v : Fin r) : Grp (Over S) :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n (labels (v, false))).toGrp ⊗
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n (labels (v, true))).toGrp

def l45FullBlockCharacters (T : Over S) :
    (T ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X) ≃*
      (∀ τ : Gal(E/ℚ), PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) :=
  (ProductPoints.Construction.groupBlockProductPointsEquiv r _ T).trans
    (MulEquiv.piCongrRight (fun v =>
      (ProductPoints.Construction.groupPairPointsEquiv _ _ T).trans (MulEquiv.prodCongr
        (((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n (labels (v, false))).app (op T)).groupIsoToMulEquiv)
        (((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n (labels (v, true))).app (op T)).groupIsoToMulEquiv)))) |>.trans
    (ProductPoints.Construction.tuplePairsMulEquiv (fun v => PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota (labels v)) n T)) |>.trans
    (ProductPoints.Construction.piReindexMulEquiv (fun τ => PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) labels)

theorem l45FullBlockCharacters_false (T : Over S)
    (a : T ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X)
    (v : Fin r) :
    l45FullBlockCharacters j iota hsplit A ρ n r labels T a (labels (v, false)) =
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n (labels (v, false))).hom.app (op T)
        (ProductPoints.Construction.groupBlockProductPointsEquiv r _ T a v ≫ fst _ _) := by
  exact Equiv.piCongrLeft_apply_apply
    (fun τ => PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) labels _ (v, false)

theorem l45FullBlockCharacters_true (T : Over S)
    (a : T ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X)
    (v : Fin r) :
    l45FullBlockCharacters j iota hsplit A ρ n r labels T a (labels (v, true)) =
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n (labels (v, true))).hom.app (op T)
        (ProductPoints.Construction.groupBlockProductPointsEquiv r _ T a v ≫ snd _ _) := by
  exact Equiv.piCongrLeft_apply_apply
    (fun τ => PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) labels _ (v, true)

theorem l45FullBlockCharacters_natural {T U : Over S} (f : T ⟶ U)
    (a : U ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X)
    (τ : Gal(E/ℚ)) :
    l45FullBlockCharacters j iota hsplit A ρ n r labels T (f ≫ a) τ =
      PELModuli.CMPoints.BlocksProjectors.blockPullback A ρ (j.localCharacter iota τ) n f
        (l45FullBlockCharacters j iota hsplit A ρ n r labels U a τ) := by
  obtain ⟨⟨v, b⟩, rfl⟩ := labels.surjective τ
  let C := l45PairedBlockFamily j iota hsplit A ρ n r labels
  have h := ProductPoints.Construction.groupBlockProductPointsEquiv_natural r C f a v
  cases b with
  | false =>
    rw [l45FullBlockCharacters_false, l45FullBlockCharacters_false]
    let e := CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n (labels (v, false))
    have hp := (congrArg (fun z => z ≫ fst
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n (labels (v, false))).X
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n (labels (v, true))).X) h).trans
        (Category.assoc _ _ _)
    exact (congrArg (fun z => e.hom.app (op T) z) hp).trans (e.hom.naturality_apply f.op _)
  | true =>
    rw [l45FullBlockCharacters_true, l45FullBlockCharacters_true]
    let e := CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n (labels (v, true))
    have hp := (congrArg (fun z => z ≫ snd
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n (labels (v, false))).X
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n (labels (v, true))).X) h).trans
        (Category.assoc _ _ _)
    exact (congrArg (fun z => e.hom.app (op T) z) hp).trans (e.hom.naturality_apply f.op _)

def l45FullBlockPointsEquiv (T : Over S) :
    (T ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X) ≃*
      A.torsionPoints (q ^ n) T :=
  (l45FullBlockCharacters j iota hsplit A ρ n r labels T).trans
    (l45TorsionPointsEquivBlocks j iota hsplit A ρ n T).symm

theorem l45FullBlockPointsEquiv_blocks (T : Over S)
    (a : T ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X) :
    l45TorsionPointsEquivBlocks j iota hsplit A ρ n T
      (l45FullBlockPointsEquiv j iota hsplit A ρ n r labels T a) =
        l45FullBlockCharacters j iota hsplit A ρ n r labels T a :=
  (l45TorsionPointsEquivBlocks j iota hsplit A ρ n T).apply_symm_apply _

theorem l45FullBlockPointsEquiv_natural {T U : Over S} (f : T ⟶ U)
    (a : U ⟶ (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)).X) :
    l45FullBlockPointsEquiv j iota hsplit A ρ n r labels T (f ≫ a) =
      A.torsionPullback (q ^ n) f (l45FullBlockPointsEquiv j iota hsplit A ρ n r labels U a) := by
  apply (l45TorsionPointsEquivBlocks j iota hsplit A ρ n T).injective
  funext τ
  exact (congrFun (l45FullBlockPointsEquiv_blocks j iota hsplit A ρ n r labels T (f ≫ a)) τ).trans
    ((l45FullBlockCharacters_natural j iota hsplit A ρ n r labels f a τ).trans
      ((congrArg (PELModuli.CMPoints.BlocksProjectors.blockPullback A ρ (j.localCharacter iota τ) n f)
        (congrFun (l45FullBlockPointsEquiv_blocks j iota hsplit A ρ n r labels U a) τ).symm).trans
          (l45TorsionPointsEquivBlocks_natural j iota hsplit A ρ n f _ τ).symm))

def l45FullBlockPointIso :
    yonedaGrp.obj (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)) ≅
      A.torsionFunctor (q ^ n) :=
  NatIso.ofComponents (fun T => (l45FullBlockPointsEquiv j iota hsplit A ρ n r labels T.unop).toGrpIso)
    (by
      intro T U f
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro a
      exact l45FullBlockPointsEquiv_natural j iota hsplit A ρ n r labels f.unop a)

/-- Native group-scheme splitting obtained from the actual idempotents. -/
def l45FullTorsionSplitting : Assembly.Construction.torsionGroup A (q ^ n) ≅
    BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels) := by
  let e : yonedaGrp.obj (BlockProducts.Construction.groupBlockProduct r (l45PairedBlockFamily j iota hsplit A ρ n r labels)) ≅
      yonedaGrp.obj (Assembly.Construction.torsionGroup A (q ^ n)) :=
    l45FullBlockPointIso j iota hsplit A ρ n r labels ≪≫ (A.torsionSchemeYonedaIso (q ^ n)).symm
  exact ((yonedaGrpFullyFaithful (C := Over S)).preimageIso e).symm

end

/-!
The full X-kernel on the actual CMPoints blocks is the native relative
Frobenius kernel. Both the total torsion splitting and each polarized
Cartier identification are constructed from the CMPoints source data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k q]
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))
variable (d r : Fin s → ℕ)
variable (e : ∀ v : Fin s, OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 (labels (v, false))).toGrp
    q 1 (d v) (r v))

def l45OrdinaryPairedFamily (v : Fin s) : OrdinaryFrobenius.Construction.NativeOrdinaryPairedBlock q k :=
  CMPointsAt.Construction.nativeOrdinaryPairOfCMPoints j iota hsplit PEL ρ (labels (v, false)) (labels (v, true))
    (hdual v) (d v) (r v) (e v)

/-- The complete ordinary decomposition has no additional splitting premise. -/
def l45OrdinaryFullSplitting : Assembly.Construction.torsionGroup PEL.abelian q ≅
    BlockProducts.Construction.groupBlockProduct s (fun v =>
      (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).chosen ⊗
        (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).opposite) :=
  eqToIso (congrArg (Assembly.Construction.torsionGroup PEL.abelian) (pow_one q).symm) ≪≫
    l45FullTorsionSplitting j iota hsplit PEL.abelian ρ 1 s labels

def l45FullXKernel : Grp (Over (Spec (.of k))) :=
  BlockProducts.Construction.groupBlockProduct s (fun v =>
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).kernel)

def l45FullXKernelInclusion :
    (l45FullXKernel j iota hsplit PEL ρ s labels hdual d r e).X ⟶ PEL.abelian.scheme :=
  OrdinaryFrobenius.Construction.fullOrdinaryPairedKernelToAbelian q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

instance l45FullXKernelInclusion_isMonHom :
    IsMonHom (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e) := by
  exact OrdinaryFrobenius.Construction.fullOrdinaryPairedKernelToAbelian_isMonHom q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

instance l45FullXKernelInclusion_closed :
    IsClosedImmersion (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e).left := by
  exact OrdinaryFrobenius.Construction.fullOrdinaryPairedKernelToAbelian_closed q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

instance l45FullXKernelInclusion_mono :
    Mono (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e) :=
  Over.mono_of_mono_left _

omit [IsAlgClosed k] [CharP k q] in
theorem l45FullXKernel_finiteLocallyFree :
    IsFinite (l45FullXKernel j iota hsplit PEL ρ s labels hdual d r e).X.hom ∧
    Flat (l45FullXKernel j iota hsplit PEL ρ s labels hdual d r e).X.hom ∧
    LocallyOfFinitePresentation (l45FullXKernel j iota hsplit PEL ρ s labels hdual d r e).X.hom :=
  BlockProducts.Construction.groupBlockProduct_finiteLocallyFree s _ (fun v =>
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).kernel_finiteLocallyFree)

/-- Equality on every test scheme, including nonreduced test schemes. -/
theorem l45FullXKernel_frobeniusKernel :
    Prescribed.Construction.PrescribedKernel (Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom
      (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e) :=
  OrdinaryFrobenius.Construction.fullOrdinaryPaired_frobeniusKernel q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

theorem l45FullXKernel_frobeniusKernel_subobject :
    Subobject.mk (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e) =
      Subobject.mk (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom) :=
  OrdinaryFrobenius.Construction.fullOrdinaryPaired_frobeniusKernel_subobject q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

def l45FullXFrobeniusQuotientIso :
    BaseChange.Construction.subgroupQuotient (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e) ≅
      (BaseChange.Construction.fppfPoints (Spec (.of k))).obj
        (PEL.abelian.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).scheme :=
  OrdinaryFrobenius.Construction.fullOrdinaryPairedFrobeniusQuotientIso q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

theorem l45FullXFrobeniusQuotientIso_projection :
    Prescribed.Construction.subgroupQuotientProjection (l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e) ≫
        (l45FullXFrobeniusQuotientIso j iota hsplit PEL ρ s labels hdual d r e).hom =
      (BaseChange.Construction.fppfPoints (Spec (.of k))).map (Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom :=
  OrdinaryFrobenius.Construction.fullOrdinaryPairedFrobeniusQuotientIso_projection q k PEL.abelian s
    (l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e)
    (l45OrdinaryFullSplitting j iota hsplit PEL ρ s labels hdual d r e)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction
