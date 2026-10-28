import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Pointed Smooth Nil Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PointedSmoothNilLift

noncomputable section

/-! A smooth lift of a map of special fibers can preserve a prescribed
section exactly. The auxiliary pullback remembers the whole source,
so its second projection is fixed throughout the nilpotent lifting. -/

universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {C : Type z} [CommRing C] [Algebra R C]
  (I : Ideal R) (πA : A →ₐ[R] C) (πB : B →ₐ[R] C)
  (εA : A →ₐ[R] R) (εB : B →ₐ[R] R) (εC : C →ₐ[R] R ⧸ I)
  (hA : εC.comp πA = (Ideal.Quotient.mkₐ R I).comp εA)
  (hB : εC.comp πB = (Ideal.Quotient.mkₐ R I).comp εB)

def extensionMap : (AlgHom.pullback εB εA) →ₐ[R]
    (AlgHom.pullback εC ((Ideal.Quotient.mkₐ R I).comp εA)) :=
  ((πB.comp (AlgHom.pullbackFst εB εA)).prod
    (AlgHom.pullbackSnd εB εA)).codRestrict _ (fun x => by
      change εC (πB x.val.1) = Ideal.Quotient.mk I (εA x.val.2)
      exact (AlgHom.congr_fun hB x.val.1).trans
        (congrArg (Ideal.Quotient.mk I) x.property))

def sourceMap : A →ₐ[R] (AlgHom.pullback εC ((Ideal.Quotient.mkₐ R I).comp εA)) :=
  (πA.prod (AlgHom.id R A)).codRestrict _ (fun a => AlgHom.congr_fun hA a)

include hB in
theorem extension_surjective (hπB : Function.Surjective πB)
    (hbase : I ≤ RingHom.ker (algebraMap R C)) :
    Function.Surjective (extensionMap I πB εA εB εC hB) := by
  intro x
  obtain ⟨b, hb⟩ := hπB x.val.1
  let d : R := εA x.val.2 - εB b
  have hd : d ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I (εA x.val.2 - εB b) = 0
    have he : Ideal.Quotient.mk I (εB b) = εC (πB b) :=
      (AlgHom.congr_fun hB b).symm
    rw [map_sub, he, hb]
    exact sub_eq_zero.mpr x.property.symm
  have hdb : πB (algebraMap R B d) = 0 := by
    rw [πB.commutes]
    exact hbase hd
  let y : AlgHom.pullback εB εA := ⟨(b + algebraMap R B d, x.val.2), by
    change εB (b + algebraMap R B d) = εA x.val.2
    rw [map_add, εB.commutes]
    change εB b + (εA x.val.2 - εB b) = εA x.val.2
    rw [add_comm, sub_add_cancel]⟩
  refine ⟨y, Subtype.ext ?_⟩
  apply Prod.ext
  · change πB (b + algebraMap R B d) = x.val.1
    rw [map_add, hdb, add_zero, hb]
  · rfl

theorem extension_kernel_nilpotent (hπB : IsNilpotent (RingHom.ker πB.toRingHom)) :
    IsNilpotent (RingHom.ker (extensionMap I πB εA εB εC hB).toRingHom) := by
  let J := RingHom.ker (extensionMap I πB εA εB εC hB).toRingHom
  let fst := (AlgHom.pullbackFst εB εA).toRingHom
  let snd := (AlgHom.pullbackSnd εB εA).toRingHom
  have hfst : J.map fst ≤ RingHom.ker πB.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change extensionMap I πB εA εB εC hB x = 0 at hx
    exact congrArg (fun y => y.val.1) hx
  have hsnd : J ≤ RingHom.ker snd := by
    intro x hx
    change extensionMap I πB εA εB εC hB x = 0 at hx
    exact congrArg (fun y => y.val.2) hx
  obtain ⟨m, hm⟩ := hπB
  change (RingHom.ker πB.toRingHom) ^ m = ⊥ at hm
  have hfstpow : J ^ (m + 1) ≤ RingHom.ker fst := by
    apply (Ideal.map_eq_bot_iff_le_ker fst).mp
    apply le_antisymm _ bot_le
    rw [Ideal.map_pow]
    calc
      (J.map fst) ^ (m + 1) ≤ (RingHom.ker πB.toRingHom) ^ (m + 1) :=
        Ideal.pow_right_mono hfst _
      _ = ⊥ := by rw [pow_succ, hm, Ideal.bot_mul]
  have hsndpow : J ^ (m + 1) ≤ RingHom.ker snd :=
    (Ideal.pow_le_self (Nat.succ_ne_zero m)).trans hsnd
  refine ⟨m + 1, le_antisymm (fun x hx => ?_) bot_le⟩
  change x = 0
  apply Subtype.ext
  exact Prod.ext (hfstpow hx) (hsndpow hx)

include hA hB in
theorem exists_lift [Algebra.FormallySmooth R A]
    (hπB : Function.Surjective πB) (hker : IsNilpotent (RingHom.ker πB.toRingHom))
    (hbase : I ≤ RingHom.ker (algebraMap R C)) :
    ∃ f : A →ₐ[R] B, πB.comp f = πA ∧ εB.comp f = εA := by
  let q := extensionMap I πB εA εB εC hB
  let a := sourceMap I πA εA εC hA
  let f := Algebra.FormallySmooth.liftOfSurjective a q
    (extension_surjective I πB εA εB εC hB hπB hbase)
    (extension_kernel_nilpotent I πB εA εB εC hB hker)
  have hf := Algebra.FormallySmooth.comp_liftOfSurjective a q
    (extension_surjective I πB εA εB εC hB hπB hbase)
    (extension_kernel_nilpotent I πB εA εB εC hB hker)
  refine ⟨(AlgHom.pullbackFst εB εA).comp f, AlgHom.ext (fun x => ?_),
    AlgHom.ext (fun x => ?_)⟩
  · exact congrArg (fun y => y.val.1) (AlgHom.congr_fun hf x)
  · have hsnd : (f x).val.2 = x := congrArg (fun y => y.val.2) (AlgHom.congr_fun hf x)
    exact (f x).property.trans (congrArg εA hsnd)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PointedSmoothNilLift
