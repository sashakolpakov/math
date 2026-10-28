import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Preimage -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Preimage.Construction

noncomputable section

/-!
An exact quotient of integral groups transports to the quotient of the
actual preimage of the target integral group in an ambient isomorphism.
This is the algebraic step relating Tate cokernels to isogeny lattices.
-/

section Preimage

variable {B V W : Type*} [AddCommGroup B] [AddCommGroup V] [AddCommGroup W]
  (iB : B →+ W) (hiB : Function.Injective iB) (F : V ≃+ W)

def preimageRangeEquiv : iB.range.comap F.toAddMonoidHom ≃+ B :=
  (AddEquiv.ofBijective (F.toAddMonoidHom.addSubgroupComap iB.range) ⟨by
    intro x y he
    apply Subtype.ext
    exact F.injective (congrArg Subtype.val he),
    F.toAddMonoidHom.addSubgroupComap_surjective iB.range F.surjective⟩).trans
    (AddMonoidHom.ofInjective hiB).symm

theorem preimageRangeEquiv_spec (x : iB.range.comap F.toAddMonoidHom) :
    iB (preimageRangeEquiv iB hiB F x) = F x.val :=
  AddMonoidHom.apply_ofInjective_symm hiB _

end Preimage

variable {A B V W K : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup V] [AddCommGroup W] [AddCommGroup K]
  (iA : A →+ V) (iB : B →+ W) (hiB : Function.Injective iB)
  (f : A →+ B) (F : V ≃+ W) (hnatural : ∀ a, F (iA a) = iB (f a))
  (δ : B →+ K) (hker : δ.ker = f.range)

def preimageQuotientProjection : iB.range.comap F.toAddMonoidHom →+ K :=
  δ.comp (preimageRangeEquiv iB hiB F).toAddMonoidHom

include f hnatural hker in
theorem preimageQuotientProjection_ker :
    (preimageQuotientProjection iB hiB F δ).ker =
      iA.range.comap (iB.range.comap F.toAddMonoidHom).subtype := by
  ext x
  change δ (preimageRangeEquiv iB hiB F x) = 0 ↔ x.val ∈ iA.range
  rw [← AddMonoidHom.mem_ker, hker]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, F.injective ?_⟩
    rw [hnatural, ha, preimageRangeEquiv_spec]
  · rintro ⟨a, ha⟩
    refine ⟨a, hiB ?_⟩
    rw [preimageRangeEquiv_spec, ← hnatural, ha]

/-- Transport an exact integral quotient through an actual ambient
isomorphism; the smaller subgroup is its original integral image. -/
def preimageRangeQuotientEquiv (hδ : Function.Surjective δ) :
    (iB.range.comap F.toAddMonoidHom) ⧸
      iA.range.comap (iB.range.comap F.toAddMonoidHom).subtype ≃+ K :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (preimageQuotientProjection_ker iA iB hiB f F hnatural δ hker).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (preimageQuotientProjection iB hiB F δ)
      (hδ.comp (preimageRangeEquiv iB hiB F).surjective))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Preimage.Construction
