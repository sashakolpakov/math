import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeEquivTransport
import OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupLattice
import Mathlib.Topology.Algebra.Group.OpenMapping

/-! # Lattice Open Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeOpenImage.Construction

noncomputable section

/-! A homomorphism with open image and finite kernel pulls lattices
back, including when the image is a proper open subgroup. -/

theorem lattice_comap_of_open_image_finite_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SigmaCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (f.range : Set H))
    [Finite f.ker] (Γ : Subgroup H) (hΓ : IntegralLattice.IsLattice Γ) : IntegralLattice.IsLattice (Γ.comap f) := by
  let r : G →* f.range := f.rangeRestrict
  have hr : Continuous r := hf.subtype_mk _
  have hsurj : Function.Surjective r := f.rangeRestrict_surjective
  let : LocallyCompactSpace f.range :=
    (f.range.isClosed_of_isOpen hopen).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hropen : IsOpenMap r := r.isOpenMap_of_sigmaCompact hsurj hr
  let j : r.ker → f.ker := fun x => ⟨x.val, congrArg (fun y : f.range => y.val) x.property⟩
  let : Finite r.ker := Finite.of_injective j (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) h)
  exact LatticeEquivTransport.Construction.lattice_comap_of_open_surjective_finite_kernel r hsurj hr hropen
    (Γ.subgroupOf f.range) (OpenSubgroupLattice.Construction.open_subgroup_intersection_lattice f.range Γ hopen hΓ)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeOpenImage.Construction
