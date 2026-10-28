import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finite Coefficient Fst -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian

noncomputable section

section

/-!
Base-changing the finite-coefficient diagram to an actual scheme family
gives an inverse system with affine transitions and the expected literal
base-change scheme as its limit.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def finiteCoefficientOverDiagram : (Finset B)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  Over.lift (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeDiagram R B) (FiniteCoefficientDiagram.Abelian.finiteCoefficientStructure R B)

def finiteCoefficientOverCone : Cone (finiteCoefficientOverDiagram R B) :=
  Over.liftCone (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeDiagram R B) (FiniteCoefficientDiagram.Abelian.finiteCoefficientStructure R B)
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeCone R B) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeCone_structure R B)

def finiteCoefficientOverConeIsLimit : IsLimit (finiteCoefficientOverCone R B) :=
  Over.isLimitLiftCone (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeDiagram R B) (FiniteCoefficientDiagram.Abelian.finiteCoefficientStructure R B)
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeCone R B) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeCone_structure R B) (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeConeIsLimit R B)

variable {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))

def finiteCoefficientFamilyDiagram : (Finset B)ᵒᵖ ⥤ Scheme :=
  finiteCoefficientOverDiagram R B ⋙ Over.pullback f ⋙ Over.forget Y

def finiteCoefficientFamilyCone : Cone (finiteCoefficientFamilyDiagram R B f) :=
  (Over.pullback f ⋙ Over.forget Y).mapCone (finiteCoefficientOverCone R B)

def finiteCoefficientFamilyConeIsLimit : IsLimit (finiteCoefficientFamilyCone R B f) :=
  isLimitOfPreserves (Over.pullback f ⋙ Over.forget Y) (finiteCoefficientOverConeIsLimit R B)

def finiteCoefficientFamilyStructure : finiteCoefficientFamilyDiagram R B f ⟶
    (Functor.const (Finset B)ᵒᵖ).obj Y where
  app s := ((Over.pullback f).obj ((finiteCoefficientOverDiagram R B).obj s)).hom
  naturality {s t} a := by
    change (((Over.pullback f).map ((finiteCoefficientOverDiagram R B).map a)).left ≫ _) = _ ≫ 𝟙 Y
    rw [Category.comp_id]
    exact Over.w _

theorem finiteCoefficientFamilyCone_structure (s : (Finset B)ᵒᵖ) :
    (finiteCoefficientFamilyCone R B f).π.app s ≫ (finiteCoefficientFamilyStructure R B f).app s =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f :=
  Over.w ((Over.pullback f).map ((finiteCoefficientOverCone R B).π.app s))

theorem finiteCoefficientFamilyCone_fst (s : (Finset B)ᵒᵖ) :
    (finiteCoefficientFamilyCone R B f).π.app s ≫
      pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ≫
      Spec.map (CommRingCat.ofHom (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop).val.toRingHom) := by
  change pullback.lift
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ≫
      Spec.map (CommRingCat.ofHom (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop).val.toRingHom))
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) _ ≫
      pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f = _
  exact pullback.lift_fst _ _ _

instance finiteCoefficientFamilyDiagram_affine_transition
    {s t : (Finset B)ᵒᵖ} (a : s ⟶ t) :
    IsAffineHom ((finiteCoefficientFamilyDiagram R B f).map a) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) f
    ((finiteCoefficientOverDiagram R B).map a)
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeDiagram_affine_transition R B a)

instance finiteCoefficientFamilyDiagram_compact [QuasiCompact f] (s : (Finset B)ᵒᵖ) :
    CompactSpace ((finiteCoefficientFamilyDiagram R B f).obj s) := by
  change CompactSpace (↥(pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f))
  infer_instance

instance finiteCoefficientFamilyDiagram_quasiSeparated [QuasiSeparated f] (s : (Finset B)ᵒᵖ) :
    QuasiSeparatedSpace ((finiteCoefficientFamilyDiagram R B f).obj s) := by
  change QuasiSeparatedSpace (pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f)

end

section

/-!
An actual morphism from a base-changed qcqs family to a scheme locally
of finite presentation is defined over finitely many coefficients.
The finite stage and both scheme-theoretic commutative squares are proved.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

theorem scheme_morphism_descends_to_finite_coefficients
    {Y X : Scheme} (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ⟶ X)
    (ha : a ≫ g = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ≫ f) :
    ∃ (s : (Finset B)ᵒᵖ) (k : (finiteCoefficientFamilyDiagram R B f).obj s ⟶ X),
      (finiteCoefficientFamilyCone R B f).π.app s ≫ k = a ∧
      k ≫ g = (finiteCoefficientFamilyStructure R B f).app s ≫ f := by
  let t := finiteCoefficientFamilyStructure R B f ≫ (Functor.const (Finset B)ᵒᵖ).map f
  have hcone : (finiteCoefficientFamilyCone R B f).π ≫ t =
      (Functor.const (Finset B)ᵒᵖ).map (a ≫ g) := by
    apply NatTrans.ext
    funext s
    change (finiteCoefficientFamilyCone R B f).π.app s ≫
      ((finiteCoefficientFamilyStructure R B f).app s ≫ f) = a ≫ g
    rw [← Category.assoc, finiteCoefficientFamilyCone_structure]
    exact ha.symm
  exact Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (finiteCoefficientFamilyDiagram R B f) t g (finiteCoefficientFamilyCone R B f)
    (finiteCoefficientFamilyConeIsLimit R B f) a hcone

theorem scheme_morphism_equality_descends_to_finite_coefficients
    {Y X : Scheme} (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (s : (Finset B)ᵒᵖ)
    (a b : (finiteCoefficientFamilyDiagram R B f).obj s ⟶ X)
    (ha : a ≫ g = (finiteCoefficientFamilyStructure R B f).app s ≫ f)
    (hb : b ≫ g = (finiteCoefficientFamilyStructure R B f).app s ≫ f)
    (hab : (finiteCoefficientFamilyCone R B f).π.app s ≫ a =
      (finiteCoefficientFamilyCone R B f).π.app s ≫ b) :
    ∃ (t : (Finset B)ᵒᵖ) (i : t ⟶ s),
      (finiteCoefficientFamilyDiagram R B f).map i ≫ a =
        (finiteCoefficientFamilyDiagram R B f).map i ≫ b :=
  Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (finiteCoefficientFamilyDiagram R B f)
    (finiteCoefficientFamilyStructure R B f ≫ (Functor.const (Finset B)ᵒᵖ).map f)
    g (finiteCoefficientFamilyCone R B f) (finiteCoefficientFamilyConeIsLimit R B f)
    a b ha.symm hb.symm hab

end

/-!
An actual endomorphism of a base-changed finitely presented qcqs family
descends to an endomorphism over a finite coefficient algebra. The result
retains the literal base projection and its exact comparison after base change.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

theorem scheme_endomorphism_descends_to_finite_coefficients
    {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]
    (k : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f)
    (hk : k ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) f =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) :
    ∃ (s : (Finset B)ᵒᵖ)
      (e : pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ⟶
        pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f),
      e ≫ pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f =
        pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ∧
      (finiteCoefficientFamilyCone R B f).π.app s ≫ e =
        k ≫ (finiteCoefficientFamilyCone R B f).π.app s := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hbase : (k ≫ pullback.snd p f) ≫ f = pullback.snd p f ≫ f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk, pullback.condition]
  obtain ⟨s, a, ha, haf⟩ := scheme_morphism_descends_to_finite_coefficients R B f f
    (k ≫ pullback.snd p f) hbase
  let a' : pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ⟶ Y := a
  let q : pullback p f ⟶ pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f :=
    (finiteCoefficientFamilyCone R B f).π.app s
  have hqfst : q ≫ pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f =
      pullback.fst p f ≫ Spec.map
        (CommRingCat.ofHom (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop).val.toRingHom) :=
    finiteCoefficientFamilyCone_fst R B f s
  have hqsnd : q ≫ pullback.snd (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f = pullback.snd p f :=
    finiteCoefficientFamilyCone_structure R B f s
  have hpair : pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ≫
      FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop = a' ≫ f :=
    (pullback.condition).trans haf.symm
  let e := pullback.lift (pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f) a' hpair
  refine ⟨s, e, pullback.lift_fst _ _ _, ?_⟩
  change q ≫ e = k ≫ q
  dsimp only [e]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, hqfst,
      ← Category.assoc, hk]
  · rw [Category.assoc, pullback.lift_snd]
    rw [Category.assoc, hqsnd]
    exact ha

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian
