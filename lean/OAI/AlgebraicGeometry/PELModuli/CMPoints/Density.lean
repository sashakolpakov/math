import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents

/-! # Density -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Connected components of the actual smooth proper geometric reduction
are irreducible. Thus one ordinary point suffices for the final open-density step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Density.connectedComponent_irreducible_of_smooth_proper
    {k : Type} [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] (x : X) :
    IrreducibleSpace (connectedComponent x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  have hopen : IsOpen (irreducibleComponent x) :=
    Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
      (ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smooth_scheme_stalk_domain f)
      finite_irreducibleComponents_of_isNoetherian
      (irreducibleComponent_mem_irreducibleComponents x)
  have heq : connectedComponent x = irreducibleComponent x :=
    Set.Subset.antisymm
      ((show IsClopen (irreducibleComponent x) from
        ⟨isClosed_irreducibleComponent, hopen⟩).connectedComponent_subset mem_irreducibleComponent)
      irreducibleComponent_subset_connectedComponent
  rw [heq]
  exact isIrreducible_iff_irreducibleSpace.mp isIrreducible_irreducibleComponent

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

theorem Models.RankThreePELModel.GoodIntegralReduction.connectedComponent_irreducible (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (x : R.geom a) : IrreducibleSpace (connectedComponent x) := by
  obtain ⟨_, _, _, _, _, _, hs, hp, _⟩ := hM.2.2 a
  let : Smooth (M.integral a).toOver.hom := hs
  let : IsProper (M.integral a).toOver.hom := hp
  let : Smooth (R.geometricFiber a).hom := R.geometricFiber_smooth a
  let : IsProper (R.geometricFiber a).hom := R.geometricFiber_proper a
  exact Density.connectedComponent_irreducible_of_smooth_proper (R.geometricFiber a).hom x

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
