import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MultiplicationFactorRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingFiberTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPELRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame

/-! # Central Fiber Factor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual central fiber isogeny is multiplication by q followed
by any full marked polarized comparison with its target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K))
  (c : Over.mk b ⟶ (D.correspondence (Local.IntegralType.central s)).cover)

include hdegree hs hgeometry hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralFiber_hom_factor
    (j : PELModuli.PELFamilyIso
      ((D.fiberFamily b (c ≫ (D.correspondence (Local.IntegralType.central s)).source)).shiftMarking
        (ZMod.unitOfCoprime q hg.2.2.1))
      (D.fiberFamily b (c ≫ (D.correspondence (Local.IntegralType.central s)).target))) :
    (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) _ _ c rfl rfl).isogeny.hom =
      ((𝟙 (D.fiberFamily b (c ≫ (D.correspondence (Local.IntegralType.central s)).source)).abelian.scheme) ^ q) ≫
        j.abelian.hom := by
  let x := c ≫ (D.correspondence (Local.IntegralType.central s)).source
  let y := c ≫ (D.correspondence (Local.IntegralType.central s)).target
  let frame := D.geometricSplitFrame hg hdegree hs hgeometry b x
  have hf := D.geometricSplitFrame_equivariant hg hdegree hs hgeometry b x
  exact PELIsogenies.PELIsogeny.hom_eq_multiplication_of_preimage hg.2.2.1 j
    (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x y c rfl rfl)
    D.reference.polarizationType (D.fiberPolarizationType hgeometry b x)
    (D.fiberPolarizationType hgeometry b y) hg.2.2.2.2
    (D.centralTatePreimage_eq_multiplication hg hgeometry hIsogenyQuotient hElementaryDivisors b x frame hf ⟨c, rfl⟩)
    (D.geometricFiber_abelian_eq_id hgeometry b y)

include hdegree hs hgeometry hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralUniversal_fiber_factor
    (j : PELModuli.PELFamilyIso ((D.sourceFamily (Local.IntegralType.central s)).shiftMarking
      (ZMod.unitOfCoprime q hg.2.2.1)) (D.targetFamily (Local.IntegralType.central s))) :
    (Over.pullback c.left).map (D.c46Isogeny hIsogenyQuotient (Local.IntegralType.central s)).isogeny.hom =
      ((𝟙 ((D.sourceFamily (Local.IntegralType.central s)).pullback c.left).abelian.scheme) ^ q) ≫
        (Over.pullback c.left).map j.abelian.hom := by
  let x := c ≫ (D.correspondence (Local.IntegralType.central s)).source
  let y := c ≫ (D.correspondence (Local.IntegralType.central s)).target
  let p := D.sourceFamilyFiberIso (Local.IntegralType.central s) x c rfl
  let r := D.targetFamilyFiberIso (Local.IntegralType.central s) y c rfl
  let jf := PELModuli.PELFamilyIso.markingFiberTransport (ZMod.unitOfCoprime q hg.2.2.1) j c.left p r
  have he := D.centralFiber_hom_factor hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors b c jf
  have hleft : (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x y c rfl rfl).isogeny.hom =
      p.abelian.hom ≫ (Over.pullback c.left).map (D.c46Isogeny hIsogenyQuotient (Local.IntegralType.central s)).isogeny.hom ≫
        r.abelian.inv := PELIsogenies.PELIsogeny.transport_hom _ _ _
  have hright := PELModuli.PELFamilyIso.markingFiberTransport_hom (ZMod.unitOfCoprime q hg.2.2.1) j c.left p r
  rw [hleft, hright] at he
  exact MarkingFiberTransport.multiplication_factor_of_transport p.abelian r.abelian _ _ q he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
