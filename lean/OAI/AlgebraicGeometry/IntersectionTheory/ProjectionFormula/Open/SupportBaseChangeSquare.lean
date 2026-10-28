import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.StalkSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.KernelSquare
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

/-! # Support Base Change Square -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChangeSquare

noncomputable section

/-! Base-change identities for the native defining support primes
transport through commuting open chart squares. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem preimage_point {X Y : Scheme} (i : X ⟶ Y) [IsOpenImmersion i]
    (B : IrreducibleCloseds Y) (h : (i ⁻¹' (B : Set Y)).Nonempty) :
    i (CycleClass.Thom.IntersectionGeometry.supportPoint (SupportDimension.preimage i B h)) = CycleClass.Thom.IntersectionGeometry.supportPoint B := by
  let A := SupportDimension.preimage i B h
  have hp := Closed.ImmersionSupport.support_point (CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ i)
  change CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ i)) =
    i (CycleClass.Geometric.GenericPoint.reducedSupportι A (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme A))) at hp
  rw [SupportDimension.imageClosure, CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq] at hp
  exact hp.symm

theorem kernel_map_at {U Y : Scheme} (i : U ⟶ Y) [IsOpenImmersion i]
    (A : IrreducibleCloseds U) (B : IrreducibleCloseds Y)
    (hAB : i (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B) (u : U) (y : Y) (hy : i u = y)
    (huA : u ∈ (A : Set U)) (hyB : y ∈ (B : Set Y)) :
    (Stalk.PrimeQuotient.kernelPrime Y B y hyB).asIdeal.map
      (eqToHom (congrArg (fun y => Y.presheaf.stalk y) hy.symm) ≫ i.stalkMap u).hom =
        (Stalk.PrimeQuotient.kernelPrime U A u huA).asIdeal := by
  subst y
  simpa only [eqToHom_refl, Category.id_comp] using StalkSupport.kernelPrime_map i A B hAB u huA hyB

theorem kernel {X Y U V : Scheme} (f : X ⟶ Y) (q : V ⟶ U)
    (i : U ⟶ Y) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : j ≫ f = q ≫ i)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (A' : IrreducibleCloseds V) (B' : IrreducibleCloseds U)
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A') = CycleClass.Thom.IntersectionGeometry.supportPoint A) (hB : i (CycleClass.Thom.IntersectionGeometry.supportPoint B') = CycleClass.Thom.IntersectionGeometry.supportPoint B)
    (v : V) (hvA : v ∈ (A' : Set V)) (hvB : q v ∈ (B' : Set U))
    (hxA : j v ∈ (A : Set X)) (hxB : f (j v) ∈ (B : Set Y))
    (hloc : (Stalk.PrimeQuotient.kernelPrime U B' (q v) hvB).asIdeal.map (q.stalkMap v).hom =
      (Stalk.PrimeQuotient.kernelPrime V A' v hvA).asIdeal) :
    (Stalk.PrimeQuotient.kernelPrime Y B (f (j v)) hxB).asIdeal.map (f.stalkMap (j v)).hom =
      (Stalk.PrimeQuotient.kernelPrime X A (j v) hxA).asIdeal := by
  let ψ := Stalk.KernelSquare.map f i q j h v
  have hb : (Stalk.PrimeQuotient.kernelPrime Y B (f (j v)) hxB).asIdeal.map ψ.hom =
      (Stalk.PrimeQuotient.kernelPrime U B' (q v) hvB).asIdeal :=
    kernel_map_at i B' B hB (q v) (f (j v))
      (congrArg (fun g : V ⟶ Y => g v) h).symm hvB hxB
  have ha := StalkSupport.kernelPrime_map j A' A hA v hvA hxA
  have he : ((Stalk.PrimeQuotient.kernelPrime Y B (f (j v)) hxB).asIdeal.map (f.stalkMap (j v)).hom).map
      (j.stalkMap v).hom = (Stalk.PrimeQuotient.kernelPrime X A (j v) hxA).asIdeal.map (j.stalkMap v).hom := by
    calc
      _ = ((Stalk.PrimeQuotient.kernelPrime Y B (f (j v)) hxB).asIdeal.map ψ.hom).map (q.stalkMap v).hom := by
        rw [Ideal.map_map, Ideal.map_map]
        exact congrArg (fun φ => (Stalk.PrimeQuotient.kernelPrime Y B (f (j v)) hxB).asIdeal.map φ)
          (congrArg CommRingCat.Hom.hom (Stalk.KernelSquare.square f i q j h v).symm)
      _ = (Stalk.PrimeQuotient.kernelPrime V A' v hvA).asIdeal := by rw [hb, hloc]
      _ = _ := ha.symm
  have he' := congrArg (fun I => I.comap (j.stalkMap v).hom) he
  simpa only [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (j.stalkMap v))] using he'

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChangeSquare
