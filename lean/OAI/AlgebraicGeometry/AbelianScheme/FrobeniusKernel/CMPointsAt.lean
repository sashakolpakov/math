import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsDuality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFrobenius
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation

/-! # CM Points At -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction

noncomputable section

section

/-!
The native equalizer blocks in the repaired CMPoints input supply the actual
chosen/opposite blocks of FrobeniusKernel. Coordinate presentations and the opposite
Cartier isomorphism are constructed from the splitting and polarization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

section Coordinates

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime]
variable {B : Grp (Over (Spec (.of k)))} [IsCommMonObj B.X] {n d r : ℕ}
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k B q n d r)

def ordinaryBlockCartierCoordinates : CartierModel.Construction.CartierCoordinates (.of k) B := by
  let M := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n d
  let E := OrdinaryBlocks.Construction.etaleOrdinaryBlock k q n r
  have hm := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock_finiteLocallyFree k q n d
  have he := OrdinaryBlocks.Construction.etaleOrdinaryBlock_finiteLocallyFree k q n r
  have : IsFinite M.X.hom := hm.1
  have : Flat M.X.hom := hm.2.1
  have : LocallyOfFinitePresentation M.X.hom := hm.2.2
  have : IsFinite E.X.hom := he.1
  have : Flat E.X.hom := he.2.1
  have : LocallyOfFinitePresentation E.X.hom := he.2.2
  have : IsFinite (M ⊗ E).X.hom := by
    change IsFinite (CategoryTheory.Limits.pullback.fst M.X.hom E.X.hom ≫ M.X.hom)
    infer_instance
  have : Flat (M ⊗ E).X.hom := by
    change Flat (CategoryTheory.Limits.pullback.fst M.X.hom E.X.hom ≫ M.X.hom)
    infer_instance
  have : LocallyOfFinitePresentation (M ⊗ E).X.hom := by
    change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.fst M.X.hom E.X.hom ≫ M.X.hom)
    infer_instance
  let f : B.X.left ⟶ (M ⊗ E).X.left := e.hom.hom.hom.left
  have : IsIso f := inferInstanceAs
    (IsIso (((Grp.forget (Over (Spec (.of k)))) ⋙ Over.forget _).map e.hom))
  have hw : f ≫ (M ⊗ E).X.hom = B.X.hom := e.hom.hom.hom.w
  have : IsFinite B.X.hom := hw ▸ (inferInstance : IsFinite (f ≫ (M ⊗ E).X.hom))
  have : Flat B.X.hom := hw ▸ (inferInstance : Flat (f ≫ (M ⊗ E).X.hom))
  have : LocallyOfFinitePresentation B.X.hom :=
    hw ▸ (inferInstance : LocallyOfFinitePresentation (f ≫ (M ⊗ E).X.hom))
  exact CartierModel.Construction.cartierCoordinates (.of k) B

end Coordinates

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (τ τc : Gal(E/ℚ))
variable (hdual : PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ (j.localCharacter iota τ) (j.localCharacter iota τc))
variable (d r : ℕ)
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 τ).toGrp q 1 d r)

/-- Actual ordinary block data with its Cartier pairing derived from the
specified source polarization, using the exact CMPoints duality input. -/
def nativeOrdinaryPairOfCMPoints : OrdinaryFrobenius.Construction.NativeOrdinaryPairedBlock q k := by
  let B := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 τ).toGrp
  let H := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 τc).toGrp
  have : IsCommMonObj B.X :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 τ).comm
  let P := ordinaryBlockCartierCoordinates e
  exact {
    chosen := B
    opposite := H
    multiplicativeHeight := d
    etaleHeight := r
    splitting := e
    coordinates := P
    pairing := CMPointsDuality.Construction.l45PolarizedCartierGroupIso PEL ρ (j.localCharacter iota τ)
      (j.localCharacter iota τc) hdual 1 B H
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ 1 τ)
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ 1 τc) P }

end

section

/-!
Every subgroup of a scalar O_E torsion block is stable under the integral
action. The scalar identity comes from CMPoints's actual idempotent equalizer
block, and stability is proved on arbitrary test schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n : ℕ) (τ : Gal(E/ℚ))

abbrev l45BlockInclusion : (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X ⟶ A.scheme :=
  PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ)

theorem l45BlockInclusion_point (T : Over S)
    (a : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op T) a).val =
      a ≫ l45BlockInclusion j iota hsplit A ρ n τ := rfl

instance l45BlockInclusion_isMonHom : IsMonHom (l45BlockInclusion j iota hsplit A ρ n τ) := by
  apply RepresentedGroups.Construction.isMonHom_of_point_operations
  · intro T
    exact congrArg Subtype.val
      (((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op T)).hom.map_one)
  · intro T a b
    exact congrArg Subtype.val
      (((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op T)).hom.map_mul a b)

/-- The integral action on the actual block is the corresponding
q-adic scalar action, including infinitesimal sections. -/
theorem l45BlockInclusion_scalar (r : NumberField.RingOfIntegers E) (T : Over S)
    (a : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    (a ≫ l45BlockInclusion j iota hsplit A ρ n τ) ≫ ρ.map r =
      (a ≫ l45BlockInclusion j iota hsplit A ρ n τ) ^
        (PadicInt.toZModPow n (j.localCharacter iota τ r)).val :=
  ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op T) a).property.2 r

/-- Thus every embedded subgroup of the block is O_E-stable. -/
theorem l45BlockSubgroup_stable (H : Grp (Over S))
    (f : H ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp)
    (r : NumberField.RingOfIntegers E) (T : Over S) (a : T ⟶ H.X) :
    ∃ a' : T ⟶ H.X,
      a' ≫ (f.hom.hom ≫ l45BlockInclusion j iota hsplit A ρ n τ) =
        (a ≫ (f.hom.hom ≫ l45BlockInclusion j iota hsplit A ρ n τ)) ≫ ρ.map r := by
  let m := (PadicInt.toZModPow n (j.localCharacter iota τ r)).val
  refine ⟨a ^ m, ?_⟩
  have hi : IsMonHom (f.hom.hom ≫ l45BlockInclusion j iota hsplit A ρ n τ) := inferInstance
  rw [MonObj.pow_comp]
  exact (congrArg (fun z => z ^ m) (Category.assoc a f.hom.hom
    (l45BlockInclusion j iota hsplit A ρ n τ)).symm).trans
      ((l45BlockInclusion_scalar j iota hsplit A ρ n τ r T (a ≫ f.hom.hom)).symm.trans
        (congrArg (fun z => z ≫ ρ.map r) (Category.assoc _ _ _)))

end

section

/-!
The actual CMPoints blocks embed compatibly across torsion levels. In
particular their q-torsion subgroups retain exactly the same source and
inclusion into A when used inside q-squared torsion for Z.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

theorem pow_padic_residue_compatible {q : ℕ} [Fact q.Prime]
    {G : Type*} [Monoid G] (x : G) {n m : ℕ} (hnm : n ≤ m)
    (hx : x ^ (q ^ n) = 1) (b : PadicInt q) :
    x ^ (PadicInt.toZModPow n b).val = x ^ (PadicInt.toZModPow m b).val := by
  let c := ZMod.castHom (pow_dvd_pow q hnm) (ZMod (q ^ n))
  have hc : c (PadicInt.toZModPow m b) = PadicInt.toZModPow n b :=
    congrArg (fun f : PadicInt q →+* ZMod (q ^ n) => f b)
      (PadicInt.zmod_cast_comp_toZModPow n m hnm)
  have hv : ((PadicInt.toZModPow m b).val : ZMod (q ^ n)) = PadicInt.toZModPow n b :=
    (map_natCast c _).symm.trans
      ((congrArg c (ZMod.natCast_zmod_val (PadicInt.toZModPow m b))).trans hc)
  exact pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).mp
    ((ZMod.natCast_zmod_val (PadicInt.toZModPow n b)).trans hv.symm)) hx

variable {O : Type} [CommRing O] {S : Scheme} {g q : ℕ} [Fact q.Prime]

theorem l45BlockPoints_mono (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (χ : O →+* PadicInt q) {n m : ℕ} (hnm : n ≤ m)
    (T : Over S) : PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ n T ≤ PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ m T := by
  intro x hx
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hd⟩ := pow_dvd_pow q hnm
    rw [hd, pow_mul, hx.1, one_pow]
  · intro a
    exact (hx.2 a).trans (pow_padic_residue_compatible x hnm hx.1 (χ a))

def l45BlockFunctorEmbedding (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (χ : O →+* PadicInt q) {n m : ℕ} (hnm : n ≤ m) :
    PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ χ n ⟶ PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ χ m where
  app T := GrpCat.ofHom (Subgroup.inclusion (l45BlockPoints_mono A ρ χ hnm T.unop))
  naturality _ _ _ := rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (τ : Gal(E/ℚ))

def l45BlockLevelEmbedding {n m : ℕ} (hnm : n ≤ m) :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ m τ).toGrp :=
  (yonedaGrpFullyFaithful (C := Over S)).preimage
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom ≫
      l45BlockFunctorEmbedding A ρ (j.localCharacter iota τ) hnm ≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ m τ).inv)

theorem l45BlockLevelEmbedding_points {n m : ℕ} (hnm : n ≤ m) (T : Over S)
    (a : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ m τ).hom.app (op T)
      (a ≫ (l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom) =
      (l45BlockFunctorEmbedding A ρ (j.localCharacter iota τ) hnm).app (op T)
        ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op T) a) := by
  have h := (yonedaGrpFullyFaithful (C := Over S)).map_preimage
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom ≫
      l45BlockFunctorEmbedding A ρ (j.localCharacter iota τ) hnm ≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ m τ).inv)
  have hc := congrArg (fun α => α ≫ (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ m τ).hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  exact congrArg (fun α => (α.app (op T)).hom a) hc

theorem l45BlockLevelEmbedding_inclusion {n m : ℕ} (hnm : n ≤ m) :
    (l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom ≫
      l45BlockInclusion j iota hsplit A ρ m τ = l45BlockInclusion j iota hsplit A ρ n τ := by
  have h := congrArg Subtype.val
    (l45BlockLevelEmbedding_points j iota hsplit A ρ τ hnm _ (𝟙 _))
  change ((𝟙 _) ≫ (l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom) ≫
      l45BlockInclusion j iota hsplit A ρ m τ =
        (𝟙 _) ≫ l45BlockInclusion j iota hsplit A ρ n τ at h
  simpa only [Category.id_comp] using h

instance l45BlockLevelEmbedding_closed {n m : ℕ} (hnm : n ≤ m) :
    IsClosedImmersion (l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom.left := by
  have : IsClosedImmersion (l45BlockInclusion j iota hsplit A ρ m τ).left :=
    PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed A ρ _ _
  have h := congrArg Over.Hom.left (l45BlockLevelEmbedding_inclusion j iota hsplit A ρ τ hnm)
  have : IsClosedImmersion
      ((l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom.left ≫
        (l45BlockInclusion j iota hsplit A ρ m τ).left) :=
    (congrArg IsClosedImmersion h).mpr (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed A ρ _ _)
  exact IsClosedImmersion.of_comp _ (l45BlockInclusion j iota hsplit A ρ m τ).left

def l45BlockToTorsion (n : ℕ) :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X ⟶ A.torsionScheme (q ^ n) :=
  (A.torsionSchemePointsEquiv (q ^ n) _).symm
    ⟨l45BlockInclusion j iota hsplit A ρ n τ, by
      change (l45BlockInclusion j iota hsplit A ρ n τ) ^ (q ^ n) = 1
      have h := ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app
        (op (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) (𝟙 _)).property.1
      simpa only [l45BlockInclusion_point, Category.id_comp] using h⟩

theorem l45BlockToTorsion_inclusion (n : ℕ) :
    l45BlockToTorsion j iota hsplit A ρ τ n ≫ A.torsionInclusion (q ^ n) =
      l45BlockInclusion j iota hsplit A ρ n τ :=
  congrArg (fun x : A.torsionPoints (q ^ n) _ => x.val)
    ((A.torsionSchemePointsEquiv (q ^ n) _).apply_symm_apply _)

/-- The native block embedding agrees with the already constructed
scheme-theoretic torsion embedding, preserving its inclusion into A. -/
theorem l45BlockLevelEmbedding_torsion {n m : ℕ} (hnm : n ≤ m) :
    (l45BlockLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom ≫
      l45BlockToTorsion j iota hsplit A ρ τ m =
        l45BlockToTorsion j iota hsplit A ρ τ n ≫ TorsionEmbedding.Construction.torsionLevelEmbedding A (pow_dvd_pow q hnm) := by
  apply (cancel_mono (A.torsionInclusion (q ^ m))).mp
  rw [Category.assoc, l45BlockToTorsion_inclusion, l45BlockLevelEmbedding_inclusion,
    Category.assoc, TorsionEmbedding.Construction.torsionLevelEmbedding_inclusion, l45BlockToTorsion_inclusion]

/-- Any chosen q-torsion subgroup, including the active etale plane,
keeps precisely its original source and map into A at level two. -/
theorem l45_levelTwo_subgroup_inclusion (H : Grp (Over S))
    (a : H ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp) :
    (a ≫ l45BlockLevelEmbedding j iota hsplit A ρ τ (show 1 ≤ 2 by decide)).hom.hom ≫
      l45BlockInclusion j iota hsplit A ρ 2 τ =
        a.hom.hom ≫ l45BlockInclusion j iota hsplit A ρ 1 τ :=
  (Category.assoc _ _ _).trans (congrArg (fun f => a.hom.hom ≫ f)
    (l45BlockLevelEmbedding_inclusion j iota hsplit A ρ τ (show 1 ≤ 2 by decide)))

end

/-!
Actual active Y and Z paired kernels in CMPoints's native polarized blocks.
Y uses each etale q-line; Z uses the same etale q-plane embedded at level
two and takes its opposite annihilator in that level-two ambient block.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (τ τc : Gal(E/ℚ))
variable (hdual : PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ (j.localCharacter iota τ) (j.localCharacter iota τc))

abbrev l45ChosenBlock (n : ℕ) :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n τ).toGrp

def l45BlockCoordinates {n d r : ℕ}
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (l45ChosenBlock j iota hsplit PEL ρ τ n) q n d r) :
    CartierModel.Construction.CartierCoordinates (.of k) (l45ChosenBlock j iota hsplit PEL ρ τ n) := by
  have : IsCommMonObj (l45ChosenBlock j iota hsplit PEL ρ τ n).X :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n τ).comm
  exact ordinaryBlockCartierCoordinates e

def l45PairingAtLevel (n : ℕ)
    (P : CartierModel.Construction.CartierCoordinates (.of k) (l45ChosenBlock j iota hsplit PEL ρ τ n)) :
    l45ChosenBlock j iota hsplit PEL ρ τc n ≅ P.dualGroup :=
  CMPointsDuality.Construction.l45PolarizedCartierGroupIso PEL ρ (j.localCharacter iota τ) (j.localCharacter iota τc)
    hdual n _ _ (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ n τ)
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ n τc) P

def activeEtalePlaneCoordinates : CartierModel.Construction.CartierCoordinates (.of k) (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q) := by
  have : IsCommMonObj (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X := ChosenOrdinaryKernels.Construction.etaleGroupScheme_commutative _ _
  have : IsFinite (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_finite _ _
  have : Etale (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  exact CartierModel.Construction.cartierCoordinates (.of k) _

def activeEtaleLineCoordinates (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    CartierModel.Construction.CartierCoordinates (.of k) (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L) := by
  have : IsCommMonObj (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X := ChosenOrdinaryKernels.Construction.etaleGroupScheme_commutative _ _
  have : IsFinite (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_finite _ _
  have : Etale (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  exact CartierModel.Construction.cartierCoordinates (.of k) _

variable (e₁ : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (l45ChosenBlock j iota hsplit PEL ρ τ 1) q 1 1 2)
variable (e₂ : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (l45ChosenBlock j iota hsplit PEL ρ τ 2) q 2 1 2)

def l45ActivePlaneAtLevelTwo : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ⟶
    l45ChosenBlock j iota hsplit PEL ρ τ 2 :=
  ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁) ≫
    l45BlockLevelEmbedding j iota hsplit PEL.abelian ρ τ (show 1 ≤ 2 by decide)

theorem l45ActivePlaneAtLevelTwo_inclusion :
    (l45ActivePlaneAtLevelTwo j iota hsplit PEL ρ τ e₁).hom.hom ≫
      l45BlockInclusion j iota hsplit PEL.abelian ρ 2 τ =
        (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁)).hom.hom ≫
          l45BlockInclusion j iota hsplit PEL.abelian ρ 1 τ :=
  l45_levelTwo_subgroup_inclusion j iota hsplit PEL.abelian ρ τ _ _

theorem l45ActivePlaneAtLevelTwo_closed :
    IsClosedImmersion (l45ActivePlaneAtLevelTwo j iota hsplit PEL ρ τ e₁).hom.hom.left := by
  have := ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane_closed k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁)
  have := l45BlockLevelEmbedding_closed j iota hsplit PEL.abelian ρ τ (show 1 ≤ 2 by decide)
  change IsClosedImmersion
    ((ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁)).hom.hom.left ≫
      (l45BlockLevelEmbedding j iota hsplit PEL.abelian ρ τ (show 1 ≤ 2 by decide)).hom.hom.left)
  infer_instance

/-- Z retains the literal q-torsion plane even in level-two ambient torsion. -/
theorem l45ActivePlaneAtLevelTwo_killed (T : Over (Spec (.of k)))
    (a : T ⟶ (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X) :
    (a ≫ (l45ActivePlaneAtLevelTwo j iota hsplit PEL ρ τ e₁).hom.hom ≫
      l45BlockInclusion j iota hsplit PEL.abelian ρ 2 τ) ^ q = 1 := by
  rw [l45ActivePlaneAtLevelTwo_inclusion]
  have h := ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PEL.abelian ρ 1 τ).hom.app (op T)
    (a ≫ (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁)).hom.hom)).property.1
  change ((a ≫ (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁)).hom.hom) ≫
    l45BlockInclusion j iota hsplit PEL.abelian ρ 1 τ) ^ (q ^ 1) = 1 at h
  simpa only [pow_one, Category.assoc] using h

def l45ActiveYKernel (L : EtaleSubgroups.Construction.ActiveEtaleLine q) : Grp (Over (Spec (.of k))) :=
  (l45BlockCoordinates j iota hsplit PEL ρ τ e₁).pairedKernel (activeEtaleLineCoordinates L)
    (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁) L)

def l45ActiveYKernelInclusion (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    l45ActiveYKernel j iota hsplit PEL ρ τ e₁ L ⟶
      l45ChosenBlock j iota hsplit PEL ρ τ 1 ⊗ l45ChosenBlock j iota hsplit PEL ρ τc 1 :=
  (l45BlockCoordinates j iota hsplit PEL ρ τ e₁).pairedKernelInclusion
    (activeEtaleLineCoordinates L) (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁) L)
    (l45PairingAtLevel j iota hsplit PEL ρ τ τc hdual 1 _)

theorem l45ActiveYKernelInclusion_closed (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    IsClosedImmersion (l45ActiveYKernelInclusion j iota hsplit PEL ρ τ τc hdual e₁ L).hom.hom.left :=
  (l45BlockCoordinates j iota hsplit PEL ρ τ e₁).pairedKernelInclusion_closed
    (activeEtaleLineCoordinates L) _ _
    (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine_closed k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁) L)

theorem l45ActiveYKernel_finiteLocallyFree (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    IsFinite (l45ActiveYKernel j iota hsplit PEL ρ τ e₁ L).X.hom ∧
      Flat (l45ActiveYKernel j iota hsplit PEL ρ τ e₁ L).X.hom ∧
        LocallyOfFinitePresentation (l45ActiveYKernel j iota hsplit PEL ρ τ e₁ L).X.hom := by
  have h := EtaleSubgroups.Construction.activeEtaleLineScheme_finiteLocallyFree (Spec (.of k)) q L
  have : IsFinite (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X.hom := h.1
  have : Flat (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X.hom := h.2.1
  have : LocallyOfFinitePresentation (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X.hom := h.2.2
  exact (l45BlockCoordinates j iota hsplit PEL ρ τ e₁).pairedKernel_finiteLocallyFree
    (activeEtaleLineCoordinates L) _

/-- The opposite part is computed with the level-two Cartier coordinates. -/
def l45ActiveZKernel : Grp (Over (Spec (.of k))) :=
  (l45BlockCoordinates j iota hsplit PEL ρ τ e₂).pairedKernel activeEtalePlaneCoordinates
    (l45ActivePlaneAtLevelTwo j iota hsplit PEL ρ τ e₁)

def l45ActiveZKernelInclusion : l45ActiveZKernel j iota hsplit PEL ρ τ e₁ e₂ ⟶
    l45ChosenBlock j iota hsplit PEL ρ τ 2 ⊗ l45ChosenBlock j iota hsplit PEL ρ τc 2 :=
  (l45BlockCoordinates j iota hsplit PEL ρ τ e₂).pairedKernelInclusion activeEtalePlaneCoordinates
    (l45ActivePlaneAtLevelTwo j iota hsplit PEL ρ τ e₁)
    (l45PairingAtLevel j iota hsplit PEL ρ τ τc hdual 2 _)

theorem l45ActiveZKernelInclusion_closed :
    IsClosedImmersion (l45ActiveZKernelInclusion j iota hsplit PEL ρ τ τc hdual e₁ e₂).hom.hom.left :=
  (l45BlockCoordinates j iota hsplit PEL ρ τ e₂).pairedKernelInclusion_closed
    activeEtalePlaneCoordinates _ _ (l45ActivePlaneAtLevelTwo_closed j iota hsplit PEL ρ τ e₁)

theorem l45ActiveZKernel_finiteLocallyFree :
    IsFinite (l45ActiveZKernel j iota hsplit PEL ρ τ e₁ e₂).X.hom ∧
      Flat (l45ActiveZKernel j iota hsplit PEL ρ τ e₁ e₂).X.hom ∧
        LocallyOfFinitePresentation (l45ActiveZKernel j iota hsplit PEL ρ τ e₁ e₂).X.hom := by
  have : IsFinite (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_finite _ _
  have : Etale (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  exact (l45BlockCoordinates j iota hsplit PEL ρ τ e₂).pairedKernel_finiteLocallyFree
    activeEtalePlaneCoordinates _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction
