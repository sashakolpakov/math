import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelDegree

/-! # Isogeny Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyType.ReferenceLatticeIsogeny

noncomputable section

/-! The actual reference lattice isogeny has the specified degree and
geometric kernel, in HilbertConstruction's native polarization-type convention. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance : IsIntegral D.abelianScheme.scheme.left := D.abelian.variety.property

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny.hasPolarizationType : p.isogeny.HasPolarizationType P.polarizationType := by
  have h := hP
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
  let (i : Fin (3 * s)) : NeZero (P.polarizationType i) := ⟨ne_of_gt (hpos i)⟩
  constructor
  · intro b
    let labels := (AddEquiv.toMultiplicative (F.latticeKernel_type hP).some.symm).trans
      p.complexKernelEquiv
    rw [RepresentationTheory.Theta.Geometric.IsogenyKernelDegree.isogeny_finrank_of_complex_labels p.isogeny _ labels b]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod,
      Fintype.card_pi, ZMod.card, pow_two]
  · intro k _ _ t
    exact p.geometricKernel k t

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyType.ReferenceLatticeIsogeny
