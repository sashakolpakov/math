import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

section

/-!
Pullback of the actual integral PEL objects. The Rosati equation is
transported through the Poincare bundle; the Lie condition is transported
through the canonical isomorphism of geometric fibers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme}

abbrev Has.PolarizedActionData.pullback (A : Has.PolarizedActionData E g δ N S)
    (f : T ⟶ S) : Has.PolarizedActionData E g δ N T where
  polarized := A.polarized.pullback f
  action := A.action.pullback f

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem BaseChange.poincareClass_pullback (A : Has.PolarizedActionData E g δ N S) (f : T ⟶ S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.pullback f).polarized.dual.poincare =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap A.polarized.dual f)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare) := by
  rw [AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
  rfl

omit [Algebra ℚ E] in
theorem BaseChange.rosati_pullback (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (f : T ⟶ S) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback f) (ρ.pullback f) := by
  dsimp only [AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation, AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback,
    AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.pullback, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
  intro a
  obtain ⟨d, hd, hpoincare, hadjoint⟩ := hρ a
  let : IsMonHom d := hd
  let : GrpObj ((Over.pullback f).obj A.dual.abelian.scheme) :=
    Functor.grpObjObj (F := Over.pullback f)
  let : GrpObj ((Over.pullback f).obj A.abelian.scheme) :=
    Functor.grpObjObj (F := Over.pullback f)
  refine ⟨(Over.pullback f).map d,
    inferInstanceAs (IsMonHom ((Over.pullback f).map d)), ?_, ?_⟩
  · let A' := (Over.pullback f).obj A.abelian.scheme
    let D' := (Over.pullback f).obj A.dual.abelian.scheme
    let q : (D' ⊗ A').left ⟶ (A.dual.abelian.scheme ⊗ A.abelian.scheme).left :=
      (A.dual.poincarePullbackOverMap f).left
    let L := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare
    let u : (D' ⊗ A').left ⟶ (D' ⊗ A').left :=
      ((Over.pullback f).map d ⊗ₘ 𝟙 A').left
    let v : (D' ⊗ A').left ⟶ (D' ⊗ A').left :=
      (𝟙 D' ⊗ₘ (Over.pullback f).map (ρ.map a)).left
    have hleft : u ≫ q = q ≫ (d ⊗ₘ 𝟙 A.abelian.scheme).left := by
      have hh : ((Over.pullback f).map d ⊗ₘ
          (Over.pullback f).map (𝟙 A.abelian.scheme)).left ≫ q =
          q ≫ (d ⊗ₘ 𝟙 A.abelian.scheme).left :=
        AbelianModuli.HilbertConstruction.Moduli.BaseChange.poincarePullbackOverMap_naturality A.dual A.dual d
          (𝟙 A.abelian.scheme) f
      rw [(Over.pullback f).map_id] at hh
      exact hh
    have hright : v ≫ q = q ≫ (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a).left := by
      have hh : ((Over.pullback f).map (𝟙 A.dual.abelian.scheme) ⊗ₘ
          (Over.pullback f).map (ρ.map a)).left ≫ q =
          q ≫ (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a).left :=
        AbelianModuli.HilbertConstruction.Moduli.BaseChange.poincarePullbackOverMap_naturality A.dual A.dual
          (𝟙 A.dual.abelian.scheme) (ρ.map a) f
      rw [(Over.pullback f).map_id] at hh
      exact hh
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        u
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        v
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q L)
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
      hleft, hright, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hpoincare]
  · exact ((Over.pullback f).map_comp _ _).symm.trans
      ((congrArg (fun m ↦ (Over.pullback f).map m) hadjoint).trans
        ((Over.pullback f).map_comp _ _))

variable {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {R : Type} [CommRing R] {iotaO : NumberField.RingOfIntegers E →+* R}
  {X Y : Over (Spec (.of R))}

omit [NumberField E] [NumberField.IsCMField E] in
theorem BaseChange.integralLieRanks_pullback
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) X.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hρ : Has.HasIntegralLieRanks P R iotaO X A ρ) (f : Y ⟶ X) :
    Has.HasIntegralLieRanks P R iotaO Y (A.pullback f.left) (ρ.pullback f.left) := by
  intro F hF hclosed j p hp τ
  have hcomp : (p ≫ f.left) ≫ X.hom = Spec.map (CommRingCat.ofHom j) := by
    rw [Category.assoc, f.w, hp]
  exact LieRankPullbackComposition.hasLieRank_of_iso (ρ.pullback (p ≫ f.left))
    ((ρ.pullback f.left).pullback p) _ (A.pullbackCompIso f.left p)
    (LieRankPullbackComposition.action_pullbackComp ρ f.left p) _ (hρ F j (p ≫ f.left) hcomp τ)

/-- Every geometric PEL condition is preserved, so this is an actual
object of the same moduli problem on the new test scheme. -/
def Has.IntegralPELObject.pullback (A : Has.IntegralPELObject P R iotaO N X)
    (f : Y ⟶ X) : Has.IntegralPELObject P R iotaO N Y where
  data := A.data.pullback f.left
  rosati := BaseChange.rosati_pullback A.data.polarized A.data.action A.rosati f.left
  lieRanks := BaseChange.integralLieRanks_pullback A.data.polarized.abelian A.data.action A.lieRanks f

variable {K : Type} [Field K] [NumberField K] {iota : E →+* K}
  {Z : Over (Spec (.of K))}

omit [NumberField E] [NumberField.IsCMField E] [NumberField K] in
/-- Over the characteristic-zero base, the integral signature condition
is exactly the ReferenceFamily condition, on the same geometric fibers. -/
theorem BaseChange.integralLieRanks_iff_prescribed
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) Z.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) :
    Has.HasIntegralLieRanks P K (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) Z A ρ ↔
      AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota Z A ρ := by
  rfl

def Has.IntegralPELObject.toCharacteristicZero
    (A : Has.IntegralPELObject P K
      (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N Z) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N Z where
  polarized := A.data.polarized
  action := A.data.action
  rosati := A.rosati
  lieRanks := BaseChange.integralLieRanks_iff_prescribed _ _ |>.mp A.lieRanks

def BaseChange.integralPELOfCharacteristicZero (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N Z) :
    Has.IntegralPELObject P K
      (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N Z where
  data := Has.characteristicZeroPELData P A
  rosati := A.rosati
  lieRanks := BaseChange.integralLieRanks_iff_prescribed _ _ |>.mpr A.lieRanks

def BaseChange.characteristicZeroPELEquiv :
    Has.IntegralPELObject P K (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N Z ≃
      AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N Z where
  toFun := Has.IntegralPELObject.toCharacteristicZero
  invFun := BaseChange.integralPELOfCharacteristicZero
  left_inv _ := rfl
  right_inv _ := rfl

end

/-! Change of the coefficient ring for the integral PEL problem, and its
actual characteristic-zero generic fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {R R' : Type} [CommRing R] [CommRing R']
  {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

/-- The PEL problem changes base using the same integral action. The Lie
characters are composed with the coefficient-ring homomorphism. -/
def Has.IntegralPELObject.baseChange (A : Has.IntegralPELObject P R iotaO N X)
    (φ : R →+* R') :
    Has.IntegralPELObject P R' (φ.comp iotaO) N
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) where
  data := A.data.pullback (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)))
  rosati := BaseChange.rosati_pullback A.data.polarized A.data.action A.rosati _
  lieRanks := by
    intro F hF hclosed j p hp τ
    let g := Spec.map (CommRingCat.ofHom φ)
    let q := pullback.fst X.hom g
    change p ≫ pullback.snd X.hom g = Spec.map (CommRingCat.ofHom j) at hp
    have hpoint : (p ≫ q) ≫ X.hom = Spec.map (CommRingCat.ofHom (j.comp φ)) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hp, ← Spec.map_comp]
      rfl
    exact LieRankPullbackComposition.hasLieRank_of_iso (A.data.action.pullback (p ≫ q))
      ((A.data.action.pullback q).pullback p) _
      (A.data.polarized.abelian.pullbackCompIso q p)
      (LieRankPullbackComposition.action_pullbackComp A.data.action q p) _
      (A.lieRanks F (j.comp φ) (p ≫ q) hpoint τ)

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  (B : Base.ArithmeticBaseExtension K κ) (iota : E →+* K)

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem BaseChange.integralEmbedding_generic :
    B.toField.comp (B.integralEmbedding iota) =
      ((algebraMap K B.extension.carrier).comp iota).comp
        (algebraMap (NumberField.RingOfIntegers E) E) := by
  ext a
  exact B.integralEmbedding_toField iota a

/-- An integral PEL family has an actual ReferenceFamily PEL object as its generic
fiber, with the required scalar action obtained from the integral embedding. -/
def Has.IntegralPELObject.genericFiber {Y : Over B.base}
    (A : Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Y) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P ((algebraMap K B.extension.carrier).comp iota) N
      ((Over.pullback B.generic).obj Y) where
  polarized := (A.baseChange B.toField).data.polarized
  action := (A.baseChange B.toField).data.action
  rosati := (A.baseChange B.toField).rosati
  lieRanks := by
    apply (BaseChange.integralLieRanks_iff_prescribed _ _).mp
    rw [← BaseChange.integralEmbedding_generic B iota]
    exact (A.baseChange B.toField).lieRanks

theorem Has.IntegralPELObject.genericFiber_data {Y : Over B.base}
    (A : Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Y) :
    Has.characteristicZeroPELData P (A.genericFiber B iota) =
      A.data.pullback (pullback.fst Y.hom B.generic) := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL
