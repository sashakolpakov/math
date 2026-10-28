import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralAlbaneseTrace

/-! # Central Marking Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The central graph identifies the actual target universal family
with the q-shifted marking of its source family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.central_target_eq_source_marking :
    (D.correspondence (Local.IntegralType.central s)).target =
      (D.correspondence (Local.IntegralType.central s)).source ≫
        (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom := by
  rw [← D.centralTargetMap_eq_marking hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors]
  exact (D.centralTargetMap_factor hg hdegree hs hgeometry hIsogenyQuotient).symm

def Data.SphericalPELAlbaneseData.centralMarkingFamilyIso :
    PELModuli.PELFamilyIso ((D.sourceFamily (Local.IntegralType.central s)).shiftMarking (ZMod.unitOfCoprime q hg.2.2.1))
      (D.targetFamily (Local.IntegralType.central s)) := by
  let a := ZMod.unitOfCoprime q hg.2.2.1
  let source := (D.correspondence (Local.IntegralType.central s)).source.left
  let target := (D.correspondence (Local.IntegralType.central s)).target.left
  let marking := (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom.left
  have he : target = source ≫ marking :=
    congrArg Over.Hom.left (D.central_target_eq_source_marking hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors)
  let e₀ := (D.family.shiftMarkingPullbackIso a source).symm
  let e₁ := ((D.markingFamilyIso hgeometry a).pullback source).symm
  let e₂ := D.family.pullbackComp marking source
  let e₃ := PELModuli.PELFamilyIso.fromEquality (congrArg (fun z => D.family.pullback z) he.symm)
  exact e₀.trans (e₁.trans (e₂.trans e₃))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
