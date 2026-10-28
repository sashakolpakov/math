import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNaturality

/-! # Affine Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineFrobenius.BigAffineCrystallineFrobenius

noncomputable section

/-! # The original geometric Frobenius on the actual completed affine PD complex -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hbase
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.coefficients p k
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison.BigAffineCrystallineComparison.complexIso p k B σ r hr hbase
local notation "φ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.complexMap p k B σ r

def complexMap : C ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj C :=
  (e).inv ≫ φ ≫ ((Q).mapHomologicalComplex (.up ℕ)).map (e).hom

theorem square : complexMap p k B σ r hr hbase ≫
      ((Q).mapHomologicalComplex (.up ℕ)).map (e).inv = (e).inv ≫ φ := by
  unfold complexMap
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

include hr hbase in
theorem original (n : ℕ) (x : (C).homology n) :
    (AffineComparison.BigAffineCrystallineComparison.homologyIso p k B σ r hr hbase n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso Q C n).hom
        (HomologicalComplex.homologyMap (complexMap p k B σ r hr hbase) n x)) =
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.bigFrobenius p k X₀ n
      ((AffineComparison.BigAffineCrystallineComparison.homologyIso p k B σ r hr hbase n).hom x) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 2} R) (.up ℕ) n
  let f := complexMap p k B σ r hr hbase
  let t := ((Q).mapHomologicalComplex (.up ℕ)).map (e).inv
  let a := HomologicalComplex.homologyMap (e).inv n
  let u := (Mapped.ComplexHomology.MappedComplexHomology.iso Q C n).hom
  let v := (Mapped.ComplexHomology.MappedComplexHomology.iso Q S n).hom
  let h := (BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n).hom
  have hc : HomologicalComplex.homologyMap t n (HomologicalComplex.homologyMap f n x) =
      HomologicalComplex.homologyMap φ n (a x) := by
    have hs := congrArg H.map (square p k B σ r hr hbase)
    rw [H.map_comp, H.map_comp] at hs
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) x
  have hn : v (HomologicalComplex.homologyMap t n (HomologicalComplex.homologyMap f n x)) =
      a (u (HomologicalComplex.homologyMap f n x)) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (Mapped.ComplexHomologyNaturality.MappedComplexHomologyNaturality.naturality Q (e).inv n))
      (HomologicalComplex.homologyMap f n x)
  have hv := congrArg h (hn.symm.trans (congrArg v hc))
  exact hv.trans (BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.original p k B σ r hr hbase n (a x))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineFrobenius.BigAffineCrystallineFrobenius
