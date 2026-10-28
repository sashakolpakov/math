import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingRestriction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairingFormula
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitIsotropy

/-! # Source Pairing Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
The assembled split pairing equals the actual source pairing when the
projectors are conjugate-adjoint. The block pairings are literal
restrictions of that source scheme map. Thus the split formula is a
conclusion rather than an assumed comparison of pairing maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u v

variable {S : Scheme.{u}} {T W : Over S} [GrpObj T] [IsCommMonObj T]
  [GrpObj W] [IsCommMonObj W]

def Annihilator.Construction.SchemeBicharacter.pointBicharacter
    (b : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := W)) (X : Over S) :
    (X ⟶ T) →* ((X ⟶ T) →* (X ⟶ W)) where
  toFun := b.pairRightHom
  map_one' := by
    apply MonoidHom.ext
    intro y
    exact b.one_left X y
  map_mul' x z := by
    apply MonoidHom.ext
    intro y
    exact b.mul_left X x z y

variable {I : Type v} [Fintype I]
  (p : I ⊕ I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
  (horth : ∀ i j, i ≠ j → p i ≫ p j = 1)
  (hcomplete : (∏ i, p i) = 𝟙 T)

theorem SourcePairingFormula.Construction.fullSplitSchemePairing_pairValue
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := BlockGroups.Construction.fixedPointScheme (p (Sum.inl i)))
      (B := BlockGroups.Construction.fixedPointScheme (p (Sum.inr i))) (W := W))
    (X : Over S) (x y : X ⟶ T) :
    (SplitIsotropy.Construction.fullSplitSchemePairing p horth hcomplete e).pairValue x y =
      ∏ i, (e i).pairValue
        (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x (Sum.inl i))
        (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X y (Sum.inr i)) /
        (e i).pairValue
          (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X y (Sum.inl i))
          (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x (Sum.inr i)) := by
  rw [SplitIsotropy.Construction.fullSplitSchemePairing, Product.Pairing.Construction.productSchemeBicharacter_pairValue]
  apply Finset.prod_congr rfl
  intro i _
  rw [SplitPairing.Construction.splitSchemeBicharacter_pairValue]
  have hf (z : X ⟶ T) : PairedProjectors.Construction.pairedProjectorPointEquiv p horth hcomplete X z i ≫ fst _ _ =
      Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X z (Sum.inl i) := lift_fst _ _
  have hg (z : X ⟶ T) : PairedProjectors.Construction.pairedProjectorPointEquiv p horth hcomplete X z i ≫ snd _ _ =
      Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X z (Sum.inr i) := lift_snd _ _
  simp only [SplitPairing.Construction.splitPairValue, hf, hg]

variable (b : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := W))

def SourcePairingFormula.Construction.sourceBlockPairing (i : I) :
    Annihilator.Construction.SchemeBicharacter (A := BlockGroups.Construction.fixedPointScheme (p (Sum.inl i)))
      (B := BlockGroups.Construction.fixedPointScheme (p (Sum.inr i))) (W := W) :=
  b.restrict (BlockGroups.Construction.fixedPointInclusion (p (Sum.inl i))) (BlockGroups.Construction.fixedPointInclusion (p (Sum.inr i)))

theorem SourcePairingFormula.Construction.sourcePairing_split_formula
    (halt : ∀ (X : Over S) (x : X ⟶ T), b.pairValue x x = 1)
    (hadjoint : ∀ (i : I ⊕ I) (X : Over S) (x y : X ⟶ T),
      b.pairValue (x ≫ p i) y = b.pairValue x (y ≫ p (Sum.swap i)))
    (X : Over S) (x y : X ⟶ T) :
    b.pairValue x y =
      (SplitIsotropy.Construction.fullSplitSchemePairing p horth hcomplete (SourcePairingFormula.Construction.sourceBlockPairing p b)).pairValue x y := by
  rw [SourcePairingFormula.Construction.fullSplitSchemePairing_pairValue]
  simp only [SourcePairingFormula.Construction.sourceBlockPairing, Annihilator.Construction.SchemeBicharacter.restrict_pairValue,
    Torsion.Decomposition.Construction.schemeProjectorPointEquiv_inclusion]
  exact SplitPairingFormula.Construction.pairing_split_projector_formula (b.pointBicharacter X)
    (fun i => IsMonHom.monoidHom (p i) X)
    (by
      intro i k hik z
      change (z ≫ p k) ≫ p i = 1
      rw [Category.assoc, horth k i hik.symm, MonObj.comp_one])
    (by
      intro z
      change (∏ i, Torsion.Decomposition.Construction.precompositionPointHom z (p i)) = z
      rw [← map_prod, hcomplete]
      exact Category.comp_id z)
    (fun i a c => hadjoint i X a c)
    (fun a c => b.skew_of_alternating halt X a c) x y

theorem SourcePairingFormula.Construction.sourcePairing_eq_fullSplit
    (halt : ∀ (X : Over S) (x : X ⟶ T), b.pairValue x x = 1)
    (hadjoint : ∀ (i : I ⊕ I) (X : Over S) (x y : X ⟶ T),
      b.pairValue (x ≫ p i) y = b.pairValue x (y ≫ p (Sum.swap i))) :
    b = SplitIsotropy.Construction.fullSplitSchemePairing p horth hcomplete (SourcePairingFormula.Construction.sourceBlockPairing p b) := by
  have he := SourcePairingFormula.Construction.sourcePairing_split_formula p horth hcomplete b halt hadjoint (T ⊗ T) (fst T T) (snd T T)
  simp only [Annihilator.Construction.SchemeBicharacter.pairValue, lift_fst_snd, Category.id_comp] at he
  have ext_hom : ∀ c d : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := W),
      c.hom = d.hom → c = d := by
    rintro ⟨c, _, _, _, _⟩ ⟨d, _, _, _, _⟩ hcd
    cases hcd
    rfl
  exact ext_hom _ _ he

/-- The same assembled subgroup is self-annihilating for the source
pairing itself, once the conjugate projectors are adjoint. -/
theorem SourcePairingFormula.Construction.sourcePairing_fullKernel_self_annihilating
    (halt : ∀ (X : Over S) (x : X ⟶ T), b.pairValue x x = 1)
    (hadjoint : ∀ (i : I ⊕ I) (X : Over S) (x y : X ⟶ T),
      b.pairValue (x ≫ p i) y = b.pairValue x (y ≫ p (Sum.swap i)))
    {P : Over S} (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P)
    (h_CartierDuality : ∀ i, (SourcePairingFormula.Construction.sourceBlockPairing p b i).flip.relativeAnnihilator
      ((SourcePairingFormula.Construction.sourceBlockPairing p b i).relativeAnnihilator (H i)) = H i) :
    b.relativeAnnihilator (SplitIsotropy.Construction.fullSplitRelativeKernel p horth hcomplete (SourcePairingFormula.Construction.sourceBlockPairing p b) H) =
      SplitIsotropy.Construction.fullSplitRelativeKernel p horth hcomplete (SourcePairingFormula.Construction.sourceBlockPairing p b) H := by
  let F := SplitIsotropy.Construction.fullSplitRelativeKernel p horth hcomplete (SourcePairingFormula.Construction.sourceBlockPairing p b) H
  exact (congrArg (fun c : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := W) => c.relativeAnnihilator F)
    (SourcePairingFormula.Construction.sourcePairing_eq_fullSplit p horth hcomplete b halt hadjoint)).trans
      (SplitIsotropy.Construction.fullSplitRelativeKernel_self_annihilating_of_CartierDuality p horth hcomplete _ H h_CartierDuality)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
