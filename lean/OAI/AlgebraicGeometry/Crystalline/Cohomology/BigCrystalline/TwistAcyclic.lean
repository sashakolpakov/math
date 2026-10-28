import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameGlobalAcyclic

/-! # Twist Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAcyclic.BigCrystallineTwistAcyclic

noncomputable section

/-! # Acyclicity of the actual frame terms over the twisted Witt base -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX

include hr hbase in
omit [LinearOrder σ] in
theorem target_term (j q : ℕ) : Subsingleton (Ext.{u + 2} A₀ ((K).X j) (q + 1)) :=
  ⟨fun x y => (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j q x).trans
    (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j q y).symm⟩

variable (b' : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (WittVector p k)))
  (e : WittVector p k ≃+* WittVector p k)
  (he : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) e.toRingHom)
  (he' : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) e.symm.toRingHom)
  (h : b' = NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k
    (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "F" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) e he he' h
local notation "A₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) b'
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ b' a

def termIso (j : ℕ) : (F).obj ((L).X j) ≅ (K).X j :=
  (HomologicalComplex.eval _ (.up ℕ) j).mapIso
    (TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W B I γ bX b' e he he' h a)

include hr hbase e he he' h in
theorem source_term (j q : ℕ) : Subsingleton (Ext.{u + 2} A₁ ((L).X j) (q + 1)) := by
  let i := NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius.extIsoCongr R
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h)
    (termIso p k B σ r b' e he he' h j) (q + 1)
  have hf := (F).mapExt_bijective_of_preservesInjectiveObjects A₁ ((L).X j) (q + 1)
  have ht := target_term p k B σ r hr hbase j q
  exact ⟨fun x y => hf.injective (i.injective (ht.elim _ _))⟩

include hr hbase in
omit [LinearOrder σ] in
theorem transported_source_term (j q : ℕ) :
    Subsingleton (Ext.{u + 2} ((F).obj A₁) ((K).X j) (q + 1)) := by
  let i := NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius.extIsoCongr R
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h)
    (Iso.refl ((K).X j)) (q + 1)
  have ht := target_term p k B σ r hr hbase j q
  exact ⟨fun x y => i.injective (ht.elim _ _)⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAcyclic.BigCrystallineTwistAcyclic
