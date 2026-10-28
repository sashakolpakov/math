import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Inv -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange
open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
section

/-! Normalize actual line-bundle classes by their restriction to the
zero section. This operation commutes with every parameter base change. -/

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (T : Over S)

def normalizedClass (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left :=
  q / Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left
    (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q)

theorem section_base_class (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left q) = q := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) = q
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T]
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q

theorem normalizedClass_zero (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (normalizedClass A T q) = 1 := by
  rw [normalizedClass, map_div, section_base_class]
  exact div_self' _

theorem normalizedClass_eq_self (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1) :
    normalizedClass A T q = q := by
  rw [normalizedClass, hq, map_one, div_one]

theorem normalizedClass_decompose (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    normalizedClass A T q * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left
      (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q) = q :=
  div_mul_cancel q _

variable {T} {U : Over S} (u : U ⟶ T)

theorem zero_class_naturality (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left q) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback u.left (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q)
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u))

theorem base_class_naturality (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left q) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst U A.scheme).left (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback u.left q) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q)
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
    (congrArg Over.Hom.left (whiskerRight_fst u A.scheme))

theorem normalizedClass_naturality (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left (normalizedClass A T q) =
      normalizedClass A U (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left q) := by
  rw [normalizedClass, map_div, base_class_naturality, normalizedClass,
    zero_class_naturality]

end

/-! Equality in the relative Picard sheaf determines the actual normalized
class. The proof constructs and descends line-bundle isomorphisms on an
affine fpqc refinement; it keeps all nonreduced parameter schemes. -/

open Opposite

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {T : Over (Spec (.of k))} [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)

theorem normalizedClass_eq_of_cover
    (R : (Scheme.fppfTopology.over (Spec (.of k))).Cover T)
    (hR : ∀ {U : Over (Spec (.of k))} (u : U ⟶ T), R.1 u →
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left q =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left r) :
    normalizedClass A T q = normalizedClass A T r := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (normalizedClass A T q)
  obtain ⟨M, hM⟩ := Quotient.exists_rep (normalizedClass A T r)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = normalizedClass A T q at hL
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = normalizedClass A T r at hM
  have heL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) hL).trans
      (normalizedClass_zero A T q)
  have heM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) hM).trans
      (normalizedClass_zero A T r)
  let eL := Classical.choice (Quotient.exact heL)
  let eM := Classical.choice (Quotient.exact heM)
  have he : ∀ {U : Over (Spec (.of k))} (u : U ⟶ T), R.1 u →
      ((Scheme.Modules.pullback (u ▷ A.scheme).left).obj L.sheaf ≅
        (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M.sheaf) := by
    intro U u hu
    have hh : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (u ▷ A.scheme).left) := by
      change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (u ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)
      rw [hL, hM, normalizedClass_naturality, normalizedClass_naturality, hR u hu]
    exact Classical.choice (Quotient.exact hh)
  obtain ⟨U, u, _, huF, huS, huQ, ⟨e⟩⟩ :=
    AffineComparison.PicardAffineComparison.exists_affine_fpqc_comparison A.scheme L.sheaf M.sheaf R he
  let := huF
  let := huS
  let := huQ
  obtain ⟨d, _, _⟩ := NormalizedPicardDescent.NormalizedPicard.normalize_descends A u L.sheaf M.sheaf eL eM e
    L.locallyTrivial M.locallyTrivial
  have hd : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := Quotient.sound ⟨d⟩
  exact hL.symm.trans (hd.trans hM)

theorem normalizedClass_eq_of_picard_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) r) :
    normalizedClass A T q = normalizedClass A T r := by
  let R : (Scheme.fppfTopology.over (Spec (.of k))).Cover T :=
    ⟨Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme) (X := op T) q r,
      Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (.of k)))
        (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)) q r h⟩
  exact normalizedClass_eq_of_cover A q r R (fun _ hu => hu)

end AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard

namespace AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! Normalized Picard-class detection persists after arbitrary base
change of a geometric abelian variety, including nonreduced bases. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace NormalizedPicard
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

theorem familyBaseChangeIso_zero {S S' : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero (A.pullback f) T).left ≫ (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T).hom =
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A ((Over.map f).obj T)).left := by
  have h : (Over.map f).map (Isogenies.NeighborCounting.PoincareNormalization.familyZero (A.pullback f) T) ≫
      (A.baseChangeFamilyIso f T).hom =
        lift (𝟙 ((Over.map f).obj T)) (A.baseChangePointsEquiv f T 1) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_fst,
        ← Functor.map_comp, Isogenies.NeighborCounting.PoincareNormalization.familyZero, lift_fst]
      exact (Over.map f).map_id T
    · rw [Category.assoc, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_snd,
        ← AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp]
      simp only [Isogenies.NeighborCounting.PoincareNormalization.familyZero, lift_snd]
  have hz : A.baseChangePointsEquiv f T 1 = 1 := (A.baseChangePointsMulEquiv f T).map_one
  rw [hz] at h
  exact congrArg Over.Hom.left h

theorem familyBaseChangeIso_zero_inv {S S' : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A ((Over.map f).obj T)).left ≫ (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv =
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero (A.pullback f) T).left := by
  rw [← familyBaseChangeIso_zero A f T, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem baseChangedClass_zero {S S' : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S')
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ (A.pullback f).scheme).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A ((Over.map f).obj T)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero (A.pullback f) T).left q := by
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, familyBaseChangeIso_zero_inv]

theorem class_eq_of_picard_eq_after_baseChange
    {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) {S : Scheme} (f : S ⟶ Spec (.of k))
    (T : Over S) [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ (A.pullback f).scheme).left)
    (hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero (A.pullback f) T).left q = 1)
    (hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero (A.pullback f) T).left r = 1)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard (A.pullback f).scheme).app (op T) q =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard (A.pullback f).scheme).app (op T) r) : q = r := by
  let : CompactSpace ((Over.map f).obj T).left := inferInstanceAs (CompactSpace T.left)
  let : QuasiSeparatedSpace ((Over.map f).obj T).left :=
    inferInstanceAs (QuasiSeparatedSpace T.left)
  let q' := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv q
  let r' := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv r
  have h' := (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f T q).symm.trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardSheafBaseChangeIso A.scheme f).hom.hom.app (op T)) h).trans
      (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f T r))
  have hq' : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A ((Over.map f).obj T)).left q' = 1 :=
    (baseChangedClass_zero A f T q).trans hq
  have hr' : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A ((Over.map f).obj T)).left r' = 1 :=
    (baseChangedClass_zero A f T r).trans hr
  have he : q' = r' := (normalizedClass_eq_self A ((Over.map f).obj T) q' hq').symm.trans
    ((normalizedClass_eq_of_picard_eq (T := (Over.map f).obj T) A q' r' h').trans
      (normalizedClass_eq_self A ((Over.map f).obj T) r' hr'))
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T).symm).injective he

end NormalizedPicard

end AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

end

end OAI
