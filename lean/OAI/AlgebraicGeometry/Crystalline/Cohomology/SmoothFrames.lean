import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames

/-! # Smooth Frames -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothFrames.SmoothCrystallineFrames

noncomputable section

/-!
# Smooth affine frames for the actual crystalline site

Every crystalline object over the residual affine chart of a smooth
Witt-algebra maps to a p-power level of that chart's PD-envelope tower.
The lift uses the actual elementwise nilpotence of the crystalline
kernel, and allows arbitrary residual restriction maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k

section Lift

variable [Algebra.Smooth (WittVector p k) A]
  (C : Type u) [CommRing C] [Algebra k C]
  (S : PD.Thickening.AffinePDThickening p k C) (f : B →ₐ[k] C)

include hbase in
/-- A smooth affine chart lifts into the ambient ring of every crystalline object over it. -/
theorem exists_algebraLift : ∃ l : A →ₐ[W] S.ring,
    S.reduction.comp l.toRingHom = f.toRingHom.comp r := by
  let : Algebra W C := ((algebraMap k C).comp WittVector.constantCoeff).toAlgebra
  let q : S.ring →ₐ[W] C :=
    { S.reduction with commutes' w := DFunLike.congr_fun S.reduction_base w }
  let a : A →ₐ[W] C :=
    { f.toRingHom.comp r with
      commutes' w := by
        change f (r (algebraMap W A w)) = algebraMap k C (WittVector.constantCoeff w)
        rw [show r (algebraMap W A w) = algebraMap k B (WittVector.constantCoeff w) from
          DFunLike.congr_fun hbase w]
        exact f.commutes _ }
  obtain ⟨l, hl⟩ := SmoothNil.SmoothNilLifting.exists_lift a q S.reduction_surjective
    (fun b hb => S.kernel_element_isNilpotent b hb)
  exact ⟨l, congrArg AlgHom.toRingHom hl⟩

def algebraLift : A →ₐ[W] S.ring :=
  (exists_algebraLift p k B A r hbase C S f).choose

theorem algebraLift_reduction :
    S.reduction.comp (algebraLift p k B A r hbase C S f).toRingHom = f.toRingHom.comp r :=
  (exists_algebraLift p k B A r hbase C S f).choose_spec

end Lift

variable (hr : Function.Surjective r)
  (X : Over (Spec (CommRingCat.of k)))
  (j : Spec (CommRingCat.of B) ⟶ X.left) [IsOpenImmersion j]
  (hj : j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)))

/-- The frame tower of the fixed affine chart, regarded inside the native site. -/
def siteFrame (n : ℕ) : Cohomology.Site.Object p k X where
  residueRing := CommRingCat.of B
  thickening := Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n
  immersion := j
  over_base := hj

variable [Algebra.Smooth (WittVector p k) A] (Q : Cohomology.Site.Object p k X)
  (f : B →ₐ[k] Q.residueRing)
  (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j = Q.immersion)

/-- A native crystalline-site map preserving the specified residual map. -/
def siteFrameMorphism (n : ℕ) (hn : (p : Q.thickening.ring) ^ (n + 1) = 0) :
    Q ⟶ siteFrame p k B A r hbase hr X j hj n where
  reducedMap := f
  ambientMap := Affine.EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B A r hr hbase Q.residueRing Q.thickening f
    (algebraLift p k B A r hbase Q.residueRing Q.thickening f)
    (algebraLift_reduction p k B A r hbase Q.residueRing Q.thickening f) n hn
  reduction_comm a := DFunLike.congr_fun
    (Affine.EnvelopeFrames.AffineEnvelopeFrames.frameMap_reduction p k B A r hr hbase Q.residueRing Q.thickening f
      (algebraLift p k B A r hbase Q.residueRing Q.thickening f)
      (algebraLift_reduction p k B A r hbase Q.residueRing Q.thickening f) n hn) a
  over_X := hf
  dp_comp := Affine.EnvelopeFrames.AffineEnvelopeFrames.frameMap_isDPMorphism p k B A r hr hbase
    Q.residueRing Q.thickening f
    (algebraLift p k B A r hbase Q.residueRing Q.thickening f)
    (algebraLift_reduction p k B A r hbase Q.residueRing Q.thickening f) n hn

include hf in
/-- Every crystalline object over the chart maps to a finite p-power frame level. -/
theorem exists_siteFrameMorphism : ∃ n : ℕ,
    ∃ g : Q ⟶ siteFrame p k B A r hbase hr X j hj n, g.reducedMap = f := by
  obtain ⟨n, hn⟩ := Q.thickening.p_nilpotent
  refine ⟨n, siteFrameMorphism p k B A r hbase hr X j hj Q f hf n ?_, rfl⟩
  rw [pow_succ, hn, zero_mul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothFrames.SmoothCrystallineFrames
