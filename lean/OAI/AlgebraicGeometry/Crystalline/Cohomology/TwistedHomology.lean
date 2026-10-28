import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyComposition
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNatTrans
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNaturality

/-! # Twisted Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistedHomology.TwistedHomologyTransport

noncomputable section

/-! # Exact coefficient transport preserves the canonical twisted homology action -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (A : C ⥤ C) [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  (B : D ⥤ D) [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (τ : A ⋙ F ≅ F ⋙ B)

local instance : PreservesFiniteLimits (A ⋙ F) := comp_preservesFiniteLimits A F
local instance : PreservesFiniteColimits (A ⋙ F) := comp_preservesFiniteColimits A F
local instance : PreservesFiniteLimits (F ⋙ B) := comp_preservesFiniteLimits F B
local instance : PreservesFiniteColimits (F ⋙ B) := comp_preservesFiniteColimits F B

variable (K : CochainComplex C ℕ)

def map (f : K ⟶ (A.mapHomologicalComplex (.up ℕ)).obj K) :
    (F.mapHomologicalComplex (.up ℕ)).obj K ⟶
      (B.mapHomologicalComplex (.up ℕ)).obj ((F.mapHomologicalComplex (.up ℕ)).obj K) :=
  (F.mapHomologicalComplex (.up ℕ)).map f ≫ (NatTrans.mapHomologicalComplex τ.hom (.up ℕ)).app K

theorem twist_homology (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ.hom (.up ℕ)).app K) n ≫
        (Mapped.ComplexHomology.MappedComplexHomology.iso B ((F.mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        B.map (Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom =
      (Mapped.ComplexHomology.MappedComplexHomology.iso F ((A.mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        F.map (Mapped.ComplexHomology.MappedComplexHomology.iso A K n).hom ≫ τ.hom.app (K.homology n) := by
  have hn := Mapped.ComplexHomologyNatTrans.MappedComplexHomologyNatTrans.naturality τ.hom K n
  rw [← Mapped.ComplexHomologyComposition.MappedComplexHomologyComposition.complex F B K n,
    ← Mapped.ComplexHomologyComposition.MappedComplexHomologyComposition.complex A F K n] at hn
  exact hn.trans (Category.assoc
    (Mapped.ComplexHomology.MappedComplexHomology.iso F ((A.mapHomologicalComplex (.up ℕ)).obj K) n).hom
    (F.map (Mapped.ComplexHomology.MappedComplexHomology.iso A K n).hom) (τ.hom.app (K.homology n)))

theorem homology_square (f : K ⟶ (A.mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) :
    HomologicalComplex.homologyMap (TwistedHomologyTransport.map A B F τ K f) n ≫
        (Mapped.ComplexHomology.MappedComplexHomology.iso B ((F.mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        B.map (Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom =
      (Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom ≫
        F.map (HomologicalComplex.homologyMap f n ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso A K n).hom) ≫
        τ.hom.app (K.homology n) := by
  let h := HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map f) n
  have ht := congrArg (fun m => h ≫ m) (twist_homology A B F τ K n)
  have hn := congrArg (fun m => m ≫ F.map (Mapped.ComplexHomology.MappedComplexHomology.iso A K n).hom ≫
      τ.hom.app (K.homology n)) (Mapped.ComplexHomologyNaturality.MappedComplexHomologyNaturality.naturality F f n)
  simp only [Category.assoc] at ht hn
  let t := HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ.hom (.up ℕ)).app K) n
  let b := (Mapped.ComplexHomology.MappedComplexHomology.iso B ((F.mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
    B.map (Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom
  have hc := congrArg (fun m => m ≫ b)
    (HomologicalComplex.homologyMap_comp ((F.mapHomologicalComplex (.up ℕ)).map f)
      ((NatTrans.mapHomologicalComplex τ.hom (.up ℕ)).app K) n)
  have hpre := hc.trans (Category.assoc h t b)
  have hr := (congrArg (fun m => (Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom ≫ m ≫
      τ.hom.app (K.homology n))
    (F.map_comp (HomologicalComplex.homologyMap f n) (Mapped.ComplexHomology.MappedComplexHomology.iso A K n).hom)).trans
      (congrArg (fun m => (Mapped.ComplexHomology.MappedComplexHomology.iso F K n).hom ≫ m)
        (Category.assoc (F.map (HomologicalComplex.homologyMap f n))
          (F.map (Mapped.ComplexHomology.MappedComplexHomology.iso A K n).hom) (τ.hom.app (K.homology n))))
  exact (hpre.trans (ht.trans hn)).trans hr.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistedHomology.TwistedHomologyTransport
