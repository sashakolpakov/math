import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineEquivalence

/-! # Small Crystalline Counit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCounit.SmallCrystallineAdapter

noncomputable section

/-! The explicit two-site round trip preserves the original ambient
divided-power ring and is naturally isomorphic to the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))}

def counitAt (U : SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X)) :
    SmallCrystallineDpow.SmallCrystallineAdapter.to65Object (SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U) ≅ U :=
  SmallCrystallineEquivalence.SmallCrystallineAdapter.to62FullyFaithful.preimageIso (SmallCrystallineEquivalence.SmallCrystallineAdapter.unitIso (SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U)).symm

def counit : SmallCrystallineDpow.SmallCrystallineAdapter.to62 (p := p) (k := k) (X := X) ⋙ SmallCrystallineDpow.SmallCrystallineAdapter.to65 ≅ 𝟭 _ :=
  NatIso.ofComponents counitAt (fun _ => by
    apply IntegralComparison.Crystalline.Site.AffineThickening.Hom.ext
    apply DFunLike.ext
    intro x
    rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCounit.SmallCrystallineAdapter
