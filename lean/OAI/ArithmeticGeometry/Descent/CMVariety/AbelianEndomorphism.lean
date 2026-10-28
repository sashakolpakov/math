import OAI.ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison
import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientTuples
import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientGroupLaws

/-! # Abelian Endomorphism -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism

noncomputable section

section

/-! Compact, separate proofs for the two stages of simultaneous group-map spreading. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  {Index : Type} [Fintype Index] {g : ℕ}

theorem finite_abelian_endomorphisms_first_stage
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (k : Index → ((A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme))
    [∀ i, IsMonHom (k i)] :
    ∃ (s : (Finset B)ᵒᵖ)
      (a : Index → ((A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme ⟶
        (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme)),
      ∀ i, CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms (AbelianCoefficientComparison.abelianCoefficientComparison R B A s)
        (CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
          (AbelianCoefficientComparison.coefficientInclusion R B s) (a i)) (k i) ∧
        IsMonHom (CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism
          (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) (AbelianCoefficientComparison.coefficientInclusion R B s) (a i)) := by
  obtain ⟨s, a, ha⟩ := FiniteCoefficientTuples.Abelian.finite_over_endomorphisms_descend_to_finite_coefficients R B A.scheme k
  exact ⟨s, a, fun i => ⟨CoefficientEndomorphismComparison.Abelian.coefficient_endomorphism_baseChange_eq R B A s (a i) (k i) (ha i),
    CoefficientEndomorphismComparison.Abelian.coefficient_endomorphism_baseChange_group R B A s (a i) (k i) (ha i)⟩⟩

theorem finite_abelian_endomorphisms_group_stage
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (a : Index → (A.scheme ⟶ A.scheme))
    (h : ∀ i, IsMonHom
      (CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (Spec.map (CommRingCat.ofHom (algebraMap R B))) (a i))) :
    ∃ (s : (Finset B)ᵒᵖ)
      (b : Index → ((A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme ⟶
        (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme)),
      ∀ i, IsMonHom (b i) ∧
        CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms (AbelianCoefficientComparison.abelianCoefficientComparison R B A s)
          (CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
            (AbelianCoefficientComparison.coefficientInclusion R B s) (b i))
          (CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (Spec.map (CommRingCat.ofHom (algebraMap R B))) (a i)) := by
  obtain ⟨s, hs⟩ := FiniteCoefficientGroupLaws.Abelian.finite_isMonHom_descends_to_finite_coefficients R B A.scheme a h
  refine ⟨s, fun i => CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) (a i),
    fun i => ⟨hs i, ?_⟩⟩
  exact CoefficientEndomorphismComparison.Abelian.abelianCoefficientComparison_conjugation R B A s (a i)

theorem abelian_iso_trans_group
    {S : Scheme} (A B C : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (e : A.scheme ≅ B.scheme) (d : B.scheme ≅ C.scheme)
    (he : IsMonHom e.hom) (hd : IsMonHom d.hom) : IsMonHom (e ≪≫ d).hom := by
  let : IsMonHom e.hom := he
  let : IsMonHom d.hom := hd
  change IsMonHom (e.hom ≫ d.hom)
  infer_instance

end

section

/-!
An actual group endomorphism of a coefficient fiber extends after two
finite coefficient extensions. The first spreads the morphism and the
second spreads its group equations. The original fiber map is recovered
under an actual group-preserving isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def twoStageCoefficientBaseMap (s t : (Finset B)ᵒᵖ) :
    Spec (CommRingCat.of
      (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop)) ⟶
        Spec (CommRingCat.of R) :=
  FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop ≫
    FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop

instance twoStageCoefficientBaseMap_locallyFiniteType (s t : (Finset B)ᵒᵖ) :
    LocallyOfFiniteType (twoStageCoefficientBaseMap R B s t) := by
  dsimp only [twoStageCoefficientBaseMap]
  infer_instance

theorem twoStageCoefficientInclusion_base (s t : (Finset B)ᵒᵖ) :
    AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t ≫
      twoStageCoefficientBaseMap R B s t =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  dsimp only [twoStageCoefficientBaseMap]
  rw [← Category.assoc, AbelianCoefficientComparison.coefficientInclusion_base]
  exact AbelianCoefficientComparison.coefficientInclusion_base R B s

def twoStageCoefficientFamily {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (s t : (Finset B)ᵒᵖ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of
      (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop))) :=
  (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).pullback
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop)

def twoStageCoefficientComparison {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (s t : (Finset B)ᵒᵖ) :
    ((twoStageCoefficientFamily R B A s t).pullback
      (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t)).scheme ≅
        (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme :=
  AbelianCoefficientComparison.abelianCoefficientComparison (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
    (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t ≪≫
      AbelianCoefficientComparison.abelianCoefficientComparison R B A s

instance twoStageCoefficientComparison_group {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (s t : (Finset B)ᵒᵖ) :
    IsMonHom (twoStageCoefficientComparison R B A s t).hom := by
  exact abelian_iso_trans_group
    ((twoStageCoefficientFamily R B A s t).pullback
      (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t))
    ((A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).pullback (AbelianCoefficientComparison.coefficientInclusion R B s))
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (AbelianCoefficientComparison.abelianCoefficientComparison (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
      (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t)
    (AbelianCoefficientComparison.abelianCoefficientComparison R B A s)
    (AbelianCoefficientComparison.abelianCoefficientComparison_group _ _ _ _) (AbelianCoefficientComparison.abelianCoefficientComparison_group _ _ _ _)

theorem finite_abelian_group_endomorphisms_spread {g : ℕ}
    {Index : Type} [Fintype Index]
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (k : Index → ((A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme))
    [∀ i, IsMonHom (k i)] :
    ∃ (s t : (Finset B)ᵒᵖ)
      (a : Index → ((twoStageCoefficientFamily R B A s t).scheme ⟶
        (twoStageCoefficientFamily R B A s t).scheme)),
      ∀ i, IsMonHom (a i) ∧
      CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms (twoStageCoefficientComparison R B A s t)
        (CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (twoStageCoefficientFamily R B A s t)
          (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t) (a i)) (k i) := by
  obtain ⟨s, a, ha⟩ := finite_abelian_endomorphisms_first_stage R B A k
  let Aₛ := A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)
  obtain ⟨t, b, hb⟩ := finite_abelian_endomorphisms_group_stage
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B Aₛ a (fun i => (ha i).2)
  refine ⟨s, t, b, fun i => ⟨(hb i).1, ?_⟩⟩
  exact CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms.trans
    (AbelianCoefficientComparison.abelianCoefficientComparison (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B Aₛ t)
    (AbelianCoefficientComparison.abelianCoefficientComparison R B A s) _ _ _ (hb i).2 (ha i).1

end

/-! Actual finite tuples, their group-preserving pullbacks, and exact fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure AbelianEndomorphismTuple (Index : Type) {g : ℕ} {S : Scheme}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) where
  map : Index → (A.scheme ⟶ A.scheme)
  group : ∀ i, IsMonHom (map i)

attribute [instance] AbelianEndomorphismTuple.group

def AbelianEndomorphismTuple.pullback
    {Index : Type} {g : ℕ} {S T : Scheme} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : AbelianEndomorphismTuple Index A) (f : T ⟶ S) :
    AbelianEndomorphismTuple Index (A.pullback f) where
  map i := CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A f (a.map i)
  group i := by
    change IsMonHom ((Over.pullback f).map (a.map i))
    infer_instance

def ConjugateAbelianTuples
    {Index : Type} {g : ℕ} {S : Scheme} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (e : A.scheme ≅ B.scheme) (a : AbelianEndomorphismTuple Index A)
    (b : AbelianEndomorphismTuple Index B) : Prop :=
  ∀ i, CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms e (a.map i) (b.map i)

theorem ConjugateAbelianTuples.trans
    {Index : Type} {g : ℕ} {S : Scheme} {A B C : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (e : A.scheme ≅ B.scheme) (d : B.scheme ≅ C.scheme)
    (a : AbelianEndomorphismTuple Index A) (b : AbelianEndomorphismTuple Index B)
    (c : AbelianEndomorphismTuple Index C)
    (he : ConjugateAbelianTuples e a b) (hd : ConjugateAbelianTuples d b c) :
    ConjugateAbelianTuples (e ≪≫ d) a c :=
  fun i => CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms.trans e d (a.map i) (b.map i) (c.map i) (he i) (hd i)

theorem AbelianEndomorphismTuple.pullback_comparison
    {Index : Type} {g : ℕ} {S T U : Scheme} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : AbelianEndomorphismTuple Index A)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p) :
    ConjugateAbelianTuples (AbelianCoefficientComparison.iteratedAbelianPullbackIso A f h p hp)
      ((a.pullback f).pullback h) (a.pullback p) :=
  fun i => CoefficientEndomorphismComparison.Abelian.iteratedAbelianPullbackIso_conjugation A f h p hp (a.map i)

theorem abelian_endomorphism_tuple_spreads
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    {Index : Type} [Fintype Index] {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (k : AbelianEndomorphismTuple Index
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))))) :
    ∃ (s t : (Finset B)ᵒᵖ) (a : AbelianEndomorphismTuple Index (twoStageCoefficientFamily R B A s t)),
      ConjugateAbelianTuples (twoStageCoefficientComparison R B A s t)
        (a.pullback (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t)) k := by
  obtain ⟨s, t, a, ha⟩ := finite_abelian_group_endomorphisms_spread R B A k.map
  exact ⟨s, t, ⟨a, fun i => (ha i).1⟩, fun i => (ha i).2⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism
