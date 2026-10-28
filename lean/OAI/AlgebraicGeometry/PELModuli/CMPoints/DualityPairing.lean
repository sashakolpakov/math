import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Duality Pairing -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

noncomputable section

section

/-!
Cartier characters are natural characters on the big site. The duality
predicate below uses the actual polarization map to the specified dual
abelian scheme, and restricts its torsion pairing to the constructed blocks.
Existence of the ambient torsion-character identification and perfection of
its restriction are conclusions; no perfect pairing is stored as data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g N q : ℕ} {δ : Fin g → ℕ} [Fact q.Prime]
  {O : Type} [CommRing O]

def cartierCharacters (F : (Over S)ᵒᵖ ⥤ GrpCat) : (Over S)ᵒᵖ ⥤ Type 1 :=
  presheafHom F
    (yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))

def restrictCharacters {F G : (Over S)ᵒᵖ ⥤ GrpCat} (i : F ⟶ G) :
    cartierCharacters G ⟶ cartierCharacters F where
  app T := ↾(fun χ => Functor.whiskerLeft (Over.forget T.unop).op i ≫ χ)
  naturality _ _ _ := by ext χ; rfl

/-- Restriction of an actual abelian-scheme homomorphism to n-torsion. -/
def homOnTorsion (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (n : ℕ) : A.torsionFunctor n ⟶ B.torsionFunctor n where
  app T := GrpCat.ofHom {
    toFun x := ⟨x.val ≫ f, by
      change (x.val ≫ f) ^ n = 1
      have hx : x.val ^ n = 1 := x.property
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]⟩
    map_one' := Subtype.ext (MonObj.one_comp _)
    map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _) }
  naturality _ _ _ := by ext x; exact Subtype.ext (Category.assoc _ _ _)

def polarizationOnTorsion (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (n : ℕ) : P.abelian.torsionFunctor n ⟶ P.dual.abelian.torsionFunctor n :=
  homOnTorsion P.abelian P.dual.abelian P.polarization.isogeny.hom n

/-- Dual endomorphisms are recognized through the actual Poincare bundle,
as in ReferenceFamily's Rosati condition. This fixes which integral action the Cartier
identification must intertwine. -/
def PoincareAdjoint (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : P.abelian.scheme ⟶ P.abelian.scheme)
    (d : P.dual.abelian.scheme ⟶ P.dual.abelian.scheme) : Prop :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 P.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 P.dual.abelian.scheme ⊗ₘ f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare)

/-- Cartier duality through the specified dual abelian scheme and the
actual polarization: its right adjoint on the two blocks is an isomorphism.
The quantification covers all finite levels and all test schemes. -/
def PolarizationDuality (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O P.abelian)
    (χ χc : O →+* PadicInt q) : Prop :=
  ∀ n : ℕ,
    ∃ e : P.dual.abelian.torsionFunctor (q ^ n) ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0} ≅
      cartierCharacters (P.abelian.torsionFunctor (q ^ n)),
      (∀ (T : Over S)
        (y z : (P.dual.abelian.torsionFunctor (q ^ n)).obj (.op T))
        (U : Over T) (x : (P.abelian.torsionFunctor (q ^ n)).obj (.op U.left)),
        (((e.hom.app (.op T)) (ULift.up (y * z))).app (.op U)) x =
          ((((e.hom.app (.op T)) (ULift.up y)).app (.op U)) x) *
          ((((e.hom.app (.op T)) (ULift.up z)).app (.op U)) x)) ∧
      (∀ a : O,
        ∃ (d : P.dual.abelian.scheme ⟶ P.dual.abelian.scheme) (hd : IsMonHom d),
          letI := hd
          PoincareAdjoint P (ρ.map a) d ∧
          Functor.whiskerRight (homOnTorsion P.dual.abelian P.dual.abelian d (q ^ n))
              (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom =
            e.hom ≫ restrictCharacters (homOnTorsion P.abelian P.abelian (ρ.map a) (q ^ n))) ∧
      IsIso
        (Functor.whiskerRight
          (BlocksProjectors.blockInclusion P.abelian ρ χc n ≫ polarizationOnTorsion P (q ^ n))
          (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫
        e.hom ≫ restrictCharacters (BlocksProjectors.blockInclusion P.abelian ρ χ n))

end

section

/-! Character-isomorphism predicates and the legacy all-base ambient
duality interface. The completed CMPoints theorem constructs its geometric
pairing from native CartierDuality and uses only `PoincareTorsionNaturalityInput`;
it does not take `PolarizedTorsionCartierInput` as a hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (m : ℕ)

abbrev TorsionCharacterIso :=
  P.dual.abelian.torsionFunctor m ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0} ≅
    cartierCharacters (P.abelian.torsionFunctor m)

def TorsionCharacterAdditive (e : TorsionCharacterIso P m) : Prop :=
  ∀ (T : Over S) (y z : (P.dual.abelian.torsionFunctor m).obj (.op T))
    (U : Over T) (x : (P.abelian.torsionFunctor m).obj (.op U.left)),
    (((e.hom.app (.op T)) (ULift.up (y * z))).app (.op U)) x =
      ((((e.hom.app (.op T)) (ULift.up y)).app (.op U)) x) *
      ((((e.hom.app (.op T)) (ULift.up z)).app (.op U)) x)

def TorsionCharacterAdjoint (e : TorsionCharacterIso P m) : Prop :=
  ∀ (f : P.abelian.scheme ⟶ P.abelian.scheme) (hf : IsMonHom f)
    (d : P.dual.abelian.scheme ⟶ P.dual.abelian.scheme) (hd : IsMonHom d),
    letI := hf
    letI := hd
    PoincareAdjoint P f d →
      Functor.whiskerRight (homOnTorsion P.dual.abelian P.dual.abelian d m)
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom =
      e.hom ≫ restrictCharacters (homOnTorsion P.abelian P.abelian f m)

/-- General Poincare torsion duality and perfection of the ambient
polarization pairing away from its degree. The bilinearity and adjoint
conditions use the actual Poincare line bundle and actual polarization. -/
def PolarizedTorsionCartierInput : Prop :=
  ∀ (S : Scheme.{0}) (g : ℕ) (δ : Fin g → ℕ) (N : ℕ)
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (m : ℕ),
    0 < m → m.Coprime (∏ i, δ i) →
      ∃ e : TorsionCharacterIso P m,
        TorsionCharacterAdditive P m e ∧ TorsionCharacterAdjoint P m e ∧
        IsIso (Functor.whiskerRight (polarizationOnTorsion P m)
          (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom)

end

/-! Composition of actual homomorphisms on torsion, and the adjoint
identity for the ambient polarization pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

theorem homOnTorsion_comp (A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : A.scheme ⟶ B.scheme) (h : B.scheme ⟶ C.scheme)
    [IsMonHom f] [IsMonHom h] (m : ℕ) :
    homOnTorsion A C (f ≫ h) m = homOnTorsion A B f m ≫ homOnTorsion B C h m := by
  ext T x
  exact Subtype.ext (Category.assoc _ _ _).symm

theorem homOnTorsion_id (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (m : ℕ) :
    homOnTorsion A A (𝟙 A.scheme) m = 𝟙 (A.torsionFunctor m) := by
  ext T x
  exact Subtype.ext (Category.comp_id _)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)

theorem rosati_on_torsion (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ) (m : ℕ)
    (a : NumberField.RingOfIntegers E) :
    ∃ (d : P.dual.abelian.scheme ⟶ P.dual.abelian.scheme) (hd : IsMonHom d),
      let := hd
      PoincareAdjoint P (ρ.map a) d ∧
      polarizationOnTorsion P m ≫ homOnTorsion P.dual.abelian P.dual.abelian d m =
        homOnTorsion P.abelian P.abelian
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)) m ≫
            polarizationOnTorsion P m := by
  obtain ⟨d, hd, hp, ha⟩ := hρ a
  let := hd
  refine ⟨d, hd, hp, ?_⟩
  change homOnTorsion _ _ _ _ ≫ homOnTorsion _ _ _ _ =
    homOnTorsion _ _ _ _ ≫ homOnTorsion _ _ _ _
  rw [← homOnTorsion_comp, ← homOnTorsion_comp]
  ext T x
  exact Subtype.ext (congrArg (fun f => x.val ≫ f) ha)

theorem polarization_character_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ)
    (m : ℕ) (e : TorsionCharacterIso P m) (he : TorsionCharacterAdjoint P m e)
    (a : NumberField.RingOfIntegers E) :
    Functor.whiskerRight
        (homOnTorsion P.abelian P.abelian
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)) m)
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫
      (Functor.whiskerRight (polarizationOnTorsion P m)
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom) =
    (Functor.whiskerRight (polarizationOnTorsion P m)
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom) ≫
      restrictCharacters (homOnTorsion P.abelian P.abelian (ρ.map a) m) := by
  obtain ⟨d, hd, hp, ha⟩ := rosati_on_torsion P ρ hρ m a
  let := hd
  have hpair := he (ρ.map a) inferInstance d hd hp
  have ht := congrArg (fun f => Functor.whiskerRight f
    (forget GrpCat ⋙ uliftFunctor.{1, 0})) ha
  rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at ht
  rw [← Category.assoc, ← ht, Category.assoc, hpair, Category.assoc]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
