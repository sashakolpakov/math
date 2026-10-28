import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistComparison
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality

/-! # Affine Frobenius Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison

noncomputable section

/-! # Original geometric Frobenius pullback on the actual affine frame sections -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X₀
local notation "a" => fun i => r (MvPolynomial.X i)

include k in
omit [Fact p.Prime] [PerfectRing k p] [Fintype σ] [LinearOrder σ] in
theorem prime_zero : (p : B) = 0 := by
  rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]

local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B (OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ bX
local notation "e" => WittVector.frobeniusEquiv p k
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k
local notation "he'" => OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism p k

omit [PerfectRing k p] [Fintype σ] [LinearOrder σ] in
theorem geometric_map : g = NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius p k X₀ :=
  (Picard.Homomorphisms.Affine.Construction.absoluteFrobenius_spec p (Fact.out : p.Prime) B (prime_zero p k B)).symm

omit [Fintype σ] [LinearOrder σ] in
theorem over_base : bF = bX ≫ Spec.map (CommRingCat.ofHom (e).toRingHom) :=
  (congrArg (fun f => f ≫ bX) (geometric_map p k B)).trans
    (NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius_over p k X₀)

local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport.BigCrystallinePullbackSheafTransport.restriction p W B B I γ bX φ
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "A₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bF
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bF a
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B I γ bX a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B I γ bF a

include hr hbase in
theorem target_term (j q : ℕ) : Subsingleton (Ext.{u + 2} A₁ ((L).X j) (q + 1)) :=
  TwistAcyclic.BigCrystallineTwistAcyclic.source_term p k B σ r hr hbase bF e (he).isDPMorphism he'
    (over_base p k B) j q

include hr hbase in
theorem transported_source_term (j q : ℕ) :
    Subsingleton (Ext.{u + 2} ((F).obj A₀) ((L).X j) (q + 1)) := by
  let i := NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius.extIsoCongr R
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (p := p) (J := I) (δ := γ) (fY := bX) g rfl)
    (Iso.refl ((L).X j)) (q + 1)
  have ht := target_term p k B σ r hr hbase j q
  exact ⟨fun x y => i.injective (ht.elim _ _)⟩

def sectionMap : FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r ⟶
    TwistComparison.BigCrystallineTwistComparison.sourceComplex p k B σ r bF :=
  Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F A₀
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (p := p) (J := I) (δ := γ) (fY := bX) g rfl).inv
    (AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p (Fact.out : p.Prime) W B σ
      (prime_zero p k B) I γ bX a)

omit [PerfectRing k p] [Fintype σ] [LinearOrder σ] in
theorem pullback_apply (n : ℕ)
    (x : NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := I) (δ := γ) bX n) :
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback (p := p) (J := I) (δ := γ) (fY := bX) g rfl n x =
    (Ext.mk₀ (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport
      (p := p) (J := I) (δ := γ) (fY := bX) g rfl).inv).precomp
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := I) (δ := γ) bF) (zero_add n)
      ((Ext.mk₀ (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport
        (p := p) (J := I) (δ := γ) (fY := bX) g rfl).hom).postcomp
        ((F).obj A₀) (add_zero n) (x.mapExactFunctor F)) :=
  Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)

include hr hbase in
theorem generic_naturality (n : ℕ) (x : (FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r).homology n) :
    (TwistComparison.BigCrystallineTwistComparison.sourceHomologyIso p k B σ r hr hbase bF e (he).isDPMorphism he'
        (over_base p k B) n).hom
      (HomologicalComplex.homologyMap (sectionMap p k B σ r) n x) =
    (Ext.mk₀ (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport
      (p := p) (J := I) (δ := γ) (fY := bX) g rfl).inv).precomp
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := I) (δ := γ) bF) (zero_add n)
      ((Ext.mk₀ (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport
        (p := p) (J := I) (δ := γ) (fY := bX) g rfl).hom).postcomp
        ((F).obj A₀) (add_zero n)
        (((TwistComparison.BigCrystallineTwistComparison.targetHomologyIso p k B σ r hr hbase n).hom x).mapExactFunctor F)) := by
  exact Acyclic.TransportNaturality.AcyclicTransportNaturality.naturality R F A₀
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (p := p) (J := I) (δ := γ) (fY := bX) g rfl).inv
    (AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p (Fact.out : p.Prime) W B σ
      (prime_zero p k B) I γ bX a) α β
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport (p := p) (J := I) (δ := γ) (fY := bX) g rfl).hom
    (AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.augmentation p (Fact.out : p.Prime) W B σ
      (prime_zero p k B) I γ bX a)
    (TwistAcyclic.BigCrystallineTwistAcyclic.target_term p k B σ r hr hbase)
    (transported_source_term p k B σ r hr hbase)
    (target_term p k B σ r hr hbase) n x

include hr hbase in
theorem naturality (n : ℕ) (x : (FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r).homology n) :
    (TwistComparison.BigCrystallineTwistComparison.sourceHomologyIso p k B σ r hr hbase bF e (he).isDPMorphism he'
        (over_base p k B) n).hom
      (HomologicalComplex.homologyMap (sectionMap p k B σ r) n x) =
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback (p := p) (J := I) (δ := γ) (fY := bX) g rfl n
      ((FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n).hom x) := by
  rw [← TwistComparison.BigCrystallineTwistComparison.targetHomologyIso_original]
  exact (generic_naturality p k B σ r hr hbase n x).trans
    (pullback_apply p k B n
      ((TwistComparison.BigCrystallineTwistComparison.targetHomologyIso p k B σ r hr hbase n).hom x)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison
