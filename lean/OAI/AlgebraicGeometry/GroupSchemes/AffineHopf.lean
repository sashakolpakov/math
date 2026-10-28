import OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale

/-! # Affine Hopf -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-!
# FiniteEtale: recover coordinate Hopf algebras from actual affine group schemes

The Hopf operations below are transported from the given scheme operations
through the proved full faithfulness of Spec. They are not independent data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k]

/-- The multiplication supplied by the original geometric group object. -/
def FiniteEtale.FiniteCommGroupScheme.givenMultiplication (G : FiniteEtale.FiniteCommGroupScheme k) := (μ[G.scheme]).left

/-- Pull the given geometric group structure back along affine Spec. -/
@[instance_reducible]
def FiniteEtale.FiniteCommGroupScheme.coordinateGroup (G : FiniteEtale.FiniteCommGroupScheme k) : GrpObj (op G.algebra) :=
  letI : (algSpec (CommRingCat.of k)).Braided := braidedAlgSpec
  (algSpec.fullyFaithful (R := CommRingCat.of k)).grpObj (op G.algebra)

/-- Commutativity is inherited from the given geometric group law. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateGroup_comm (G : FiniteEtale.FiniteCommGroupScheme k) :
    letI := G.coordinateGroup
    IsCommMonObj (op G.algebra) := by
  let : (algSpec (CommRingCat.of k)).Braided := braidedAlgSpec
  let := G.coordinateGroup
  constructor
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  change (algSpec (CommRingCat.of k)).map
      ((β_ (op G.algebra) (op G.algebra)).hom ≫
        (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
          (Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of k)) _ _ ≫ μ[G.scheme])) = _
  rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.map_braiding]
  simp [Category.assoc]

/-- The coordinate Hopf algebra defined by the actual group scheme laws. -/
@[instance_reducible]
def FiniteEtale.FiniteCommGroupScheme.coordinateHopf (G : FiniteEtale.FiniteCommGroupScheme k) : HopfAlgebra k G.algebra := by
  let : GrpObj (op G.algebra) := G.coordinateGroup
  exact ((commHopfAlgCatEquivCogrpCommAlgCat k).inverse.obj
    (op (Grp.mk (op G.algebra)))).hopfAlgebra

/-- Reconstruction preserves the original k-algebra structure. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateHopf_algebra (G : FiniteEtale.FiniteCommGroupScheme k) :
    G.coordinateHopf.toAlgebra = (inferInstance : Algebra k G.algebra) := rfl

/-- The reconstructed coalgebra with the original scalar action made explicit. -/
@[instance_reducible]
def FiniteEtale.FiniteCommGroupScheme.coordinateCoalgebra (G : FiniteEtale.FiniteCommGroupScheme k) : Coalgebra k G.algebra := by
  exact G.coordinateHopf.toCoalgebra

/-- The recovered coordinate Hopf algebra is cocommutative. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateHopf_cocomm (G : FiniteEtale.FiniteCommGroupScheme k) :
    letI := G.coordinateCoalgebra
    Coalgebra.IsCocomm k G.algebra := by
  let := G.coordinateCoalgebra
  let := G.coordinateGroup
  have : IsCommMonObj (op G.algebra) := G.coordinateGroup_comm
  constructor
  have h := congrArg (fun f => f.unop.hom.toLinearMap)
    (IsCommMonObj.mul_comm (op G.algebra))
  exact h

/-- The reconstructed comultiplication represents the original scheme multiplication. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateHopf_represents_mul (G : FiniteEtale.FiniteCommGroupScheme k) :
    letI := G.coordinateHopf
    (pullbackSpecIso (CommRingCat.of k) (CommRingCat.of G.algebra)
      (CommRingCat.of G.algebra)).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k G.algebra).toRingHom) =
      G.givenMultiplication := by
  let := G.coordinateHopf
  let : (algSpec (CommRingCat.of k)).Braided := braidedAlgSpec
  have h' := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage
    (Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of k)) (op G.algebra) (op G.algebra) ≫
      μ[G.scheme])
  have hc := congrArg
    (fun f => Functor.LaxMonoidal.μ (algSpec (CommRingCat.of k))
      (op G.algebra) (op G.algebra) ≫ f) h'
  simp only [Functor.Monoidal.μ_δ_assoc] at hc
  exact congrArg Over.Hom.left hc

end

end OAI.AlgebraicGeometry.GroupSchemes
