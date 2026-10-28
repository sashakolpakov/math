import OAI.NumberTheory.Quaternion.Arithmetic.Adelic
import OAI.NumberTheory.Quaternion.Arithmetic.RationalIntegralStabilizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete

/-! # Archimedean Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanProjection

noncomputable section

/-! The archimedean projection of the actual S-arithmetic subgroup
is faithful. Its integral part lands in the standard arithmetic lattice. -/

open scoped Classical _root_.NumberField
open OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction _root_.NumberField IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def localProductArchimedeanMap (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ v : InfinitePlace F, Sum.inl v ∈ S) :
    Ambient.OmittedLocalProduct G S →* G.ArchimedeanProduct Set.univ where
  toFun g v := g ⟨Sum.inl v.val, harch v.val⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem localProductArchimedeanMap_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ v : InfinitePlace F, Sum.inl v ∈ S) : Continuous (localProductArchimedeanMap G S harch) :=
  continuous_pi (fun v : (Set.univ : Set (InfinitePlace F)) =>
    continuous_apply (⟨Sum.inl v.val, harch v.val⟩ : (S : Set (LocalAdeles.Place F))))

theorem arithmetic_archimedeanProjection_injective (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ v : InfinitePlace F, Sum.inl v ∈ S) :
    Function.Injective ((localProductArchimedeanMap G S harch).comp (Adelic.sArithmeticLocalSubgroup G S).subtype) := by
  intro y z he
  obtain ⟨q, _, hq⟩ := (Adelic.sArithmeticLocalSubgroup_mem G S y.val).mp y.property
  obtain ⟨r, _, hr⟩ := (Adelic.sArithmeticLocalSubgroup_mem G S z.val).mp z.property
  let v : InfinitePlace F := Classical.choice inferInstance
  have hv := congrFun he (⟨v, mem_univ v⟩ : (Set.univ : Set (InfinitePlace F)))
  have hqr : q = r := LocalAdeles.diagonalLocal_injective G (.inl v)
    ((hq ⟨Sum.inl v, harch v⟩).trans (hv.trans (hr ⟨Sum.inl v, harch v⟩).symm))
  apply Subtype.ext
  funext w
  exact (hq w).symm.trans ((congrArg (LocalAdeles.diagonalLocal G w.val) hqr).trans (hr w))

def integralLocalProductSubgroup (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Subgroup (Ambient.OmittedLocalProduct G S) where
  carrier := {g | ∀ v, g v ∈ LocalAdeles.integralLocalSubgroup G v.val}
  one_mem' v := (LocalAdeles.integralLocalSubgroup G v.val).one_mem
  mul_mem' hg hh v := (LocalAdeles.integralLocalSubgroup G v.val).mul_mem (hg v) (hh v)
  inv_mem' hg v := (LocalAdeles.integralLocalSubgroup G v.val).inv_mem (hg v)

theorem integralLocalProductSubgroup_isOpen (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    IsOpen (integralLocalProductSubgroup G S : Set (Ambient.OmittedLocalProduct G S)) := by
  change IsOpen {g : Ambient.OmittedLocalProduct G S | ∀ v, g v ∈ LocalAdeles.integralLocalSubgroup G v.val}
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun v => (LocalAdeles.integralLocalSubgroup_isOpen G v.val).preimage (continuous_apply v))

theorem integral_arithmetic_archimedean_mem (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ v : InfinitePlace F, Sum.inl v ∈ S) (g : Adelic.sArithmeticLocalSubgroup G S)
    (hg : g.val ∈ integralLocalProductSubgroup G S) :
    localProductArchimedeanMap G S harch g.val ∈
      (G.latticeStabilizer (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n)).map (G.diagonal Set.univ) := by
  obtain ⟨q, hq, he⟩ := (Adelic.sArithmeticLocalSubgroup_mem G S g.val).mp g.property
  have hstd : q ∈ G.latticeStabilizer (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n) := by
    apply RationalIntegralStabilizer.rational_integralAtAll_mem_standard_stabilizer G q
    intro v
    by_cases hv : Sum.inr v ∈ S
    · exact (he ⟨Sum.inr v, hv⟩).symm ▸ hg ⟨Sum.inr v, hv⟩
    · exact hq (.inr v) hv
  refine ⟨q, hstd, ?_⟩
  funext v
  exact he ⟨Sum.inl v.val, harch v.val⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanProjection
