import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechHomologyMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.Local

/-! # Cech Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechHomology.Comparison

noncomputable section

/-! Actual crystalline and de Rham homology presheaves have isomorphic Cech complexes on the original cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0)) (i : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCover.nerve k X
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex.complex p k X
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex (OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X) 0 I

local instance coefficientLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 2} R) :=
  fun T => (coefficientLimits p k).has_limits_of_shape (Discrete T)

def target : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  (FormalCoproduct.cochainComplexFunctor E).obj ((L).homology i)

def family (n : SimplexCategory) (t : ((E).obj (op n)).I) :
    ((D).homology i).obj (op (((E).obj (op n)).obj t)) ⟶
      ((L).homology i).obj (op (((E).obj (op n)).obj t)) :=
  CechHomologyMaps.map p k X I i n.len t

theorem family_naturality {m n : SimplexCategory} (f : m ⟶ n) (t : ((E).obj (op n)).I) :
    ((D).homology i).map (((E).map f.op).φ t).op ≫ family p k X I i n t =
      family p k X I i m (((E).map f.op).f t) ≫ ((L).homology i).map (((E).map f.op).φ t).op :=
  CechHomologyMaps.naturality p k X I i m.len n.len (((E).map f.op).f t) t
    (leOfHom (((E).map f.op).φ t))

instance family_isIso (n : SimplexCategory) (t : ((E).obj (op n)).I) :
    IsIso (family p k X I i n t) :=
  CechHomologyMaps.map_isIso p k X I i n.len t

def map : Crystalline.CechCover.deRhamHomologyComplex p k X i ⟶ target p k X I i :=
  Cech.Local.Comparison.map E ((D).homology i) ((L).homology i)
    (family p k X I i) (family_naturality p k X I i)

instance map_isIso : IsIso (Comparison.map p k X I i) :=
  Cech.Local.Comparison.map_isIso E ((D).homology i) ((L).homology i)
    (family p k X I i) (family_naturality p k X I i)

def iso : Crystalline.CechCover.deRhamHomologyComplex p k X i ≅ target p k X I i :=
  asIso (Comparison.map p k X I i)

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (q : ℕ) :
    Module.Finite R ((target p k X I i).homology q) := by
  let : Module.Finite R ((Crystalline.CechCover.deRhamHomologyComplex p k X i).homology q) :=
    Crystalline.CechCover.deRhamHomology_finite p k X hprojective i q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (iso p k X I i) q).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechHomology.Comparison
