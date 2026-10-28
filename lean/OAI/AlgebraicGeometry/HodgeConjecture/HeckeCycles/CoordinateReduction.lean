import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimePowerCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps

/-! # Coordinate Reduction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoordinateReduction.CM

/-! Reduction of standard torsion coordinates to their first level,
and the exact relation between its kernel and the top-power map. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionGenerators.CM

theorem first_divides (q n : ℕ) : q ^ 1 ∣ q ^ (n + 1) :=
  ⟨q ^ n, by rw [pow_one, pow_succ']⟩

def firstReduction (q n g : ℕ) : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g →* TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g where
  toFun x := Multiplicative.ofAdd (fun i =>
    ZMod.castHom (first_divides q n) (ZMod (q ^ 1)) (x.toAdd i))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    change ZMod.castHom (first_divides q n) (ZMod (q ^ 1)) 0 = 0
    exact map_zero (ZMod.castHom (first_divides q n) (ZMod (q ^ 1)))
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    change ZMod.castHom (first_divides q n) (ZMod (q ^ 1)) (x.toAdd i + y.toAdd i) =
      ZMod.castHom (first_divides q n) (ZMod (q ^ 1)) (x.toAdd i) +
      ZMod.castHom (first_divides q n) (ZMod (q ^ 1)) (y.toAdd i)
    exact map_add (ZMod.castHom (first_divides q n) (ZMod (q ^ 1))) (x.toAdd i) (y.toAdd i)

theorem firstReduction_generator (q n g : ℕ) (i : Fin g) :
    firstReduction q n g (TorsionGenerators.CM.generator q (n + 1) g i) = TorsionGenerators.CM.generator q 1 g i := by
  apply Multiplicative.toAdd.injective
  funext j
  change ZMod.castHom (first_divides q n) (ZMod (q ^ 1))
    ((Pi.single i (1 : ZMod (q ^ (n + 1))) : Fin g → ZMod (q ^ (n + 1))) j) =
    ((Pi.single i (1 : ZMod (q ^ 1)) : Fin g → ZMod (q ^ 1)) j)
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same, map_one]
  · simp only [Pi.single_eq_of_ne hji, map_zero]

theorem top_power_of_firstReduction_one (q n g : ℕ) (hq : 0 < q)
    (x : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g) (hx : firstReduction q n g x = 1) :
    x ^ (q ^ n) = 1 := by
  let : NeZero (q ^ (n + 1)) := ⟨pow_ne_zero _ hq.ne'⟩
  apply Multiplicative.toAdd.injective
  funext i
  have hi : ZMod.castHom (first_divides q n) (ZMod (q ^ 1)) (x.toAdd i) = 0 :=
    congrArg (fun z : TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g => z.toAdd i) hx
  have hz : ((x.toAdd i).val : ZMod (q ^ 1)) = 0 := by
    rw [← map_natCast (ZMod.castHom (first_divides q n) (ZMod (q ^ 1))), ZMod.natCast_zmod_val]
    exact hi
  have hd₁ := (ZMod.natCast_eq_zero_iff (x.toAdd i).val (q ^ 1)).mp hz
  have hd : q ∣ (x.toAdd i).val :=
    (congrArg (fun d : ℕ => d ∣ (x.toAdd i).val) (pow_one q)).mp hd₁
  obtain ⟨r, hr⟩ := hd
  have hm : q ^ (n + 1) ∣ q ^ n * (x.toAdd i).val :=
    ⟨r, by rw [hr, pow_succ, Nat.mul_assoc]⟩
  have hmz := (ZMod.natCast_eq_zero_iff (q ^ n * (x.toAdd i).val) (q ^ (n + 1))).mpr hm
  change (q ^ n) • x.toAdd i = 0
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hmz

theorem first_torsion_divisible (q n g : ℕ) (hq : 0 < q)
    (x : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g) (hx : x ^ q = 1) :
    ∃ y : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g, y ^ (q ^ n) = x := by
  classical
  have hi (i : Fin g) : q • x.toAdd i = 0 :=
    congrArg (fun z : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g => z.toAdd i) hx
  choose r hr using fun i => PrimePowerCoordinates.CM.first_torsion_coordinates q n hq (x.toAdd i) (hi i)
  refine ⟨Multiplicative.ofAdd (fun i => (r i).val), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  change (q ^ n) • ((r i).val : ZMod (q ^ (n + 1))) = x.toAdd i
  rw [nsmul_eq_mul, Nat.cast_pow]
  exact (hr i).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoordinateReduction.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoordinateReduction.CM.LiftedInjectivity

/-! Lifted geometric torsion coordinates are injective when their
first-level generators give injective coordinates. The reduction square
is proved from the actual generator equations. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionGenerators.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoordinateReduction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.FirstLevel

variable {A : Type*} [CommGroup A]

theorem reduction_square (q n g : ℕ) (hq : q ≠ 0)
    (baseMap : TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q)
    (f : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)))
    (hgen : ∀ i, TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (f (TorsionGenerators.CM.generator q (n + 1) g i)) =
      baseMap (TorsionGenerators.CM.generator q 1 g i)) :
    (TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n).comp f = baseMap.comp (firstReduction q n g) := by
  apply TorsionGenerators.CM.hom_ext q (n + 1) g hq
  intro i
  change TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (f (TorsionGenerators.CM.generator q (n + 1) g i)) =
    baseMap (firstReduction q n g (TorsionGenerators.CM.generator q (n + 1) g i))
  rw [firstReduction_generator]
  exact hgen i

theorem first_torsion_kernel (q n g : ℕ) (hq : 0 < q)
    (baseMap : TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q)
    (hb : Function.Injective baseMap)
    (f : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)))
    (hgen : ∀ i, TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (f (TorsionGenerators.CM.generator q (n + 1) g i)) =
      baseMap (TorsionGenerators.CM.generator q 1 g i))
    (x : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g) (hx : x ^ q = 1) (hfx : f x = 1) : x = 1 := by
  obtain ⟨y, hy⟩ := first_torsion_divisible q n g hq x hx
  have hfy : f y ^ (q ^ n) = 1 := by
    rw [← map_pow, hy, hfx]
  have hfirst : TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (f y) = 1 :=
    Subtype.ext (congrArg (fun z : AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)) => z.val) hfy)
  have hsquare := DFunLike.congr_fun (reduction_square q n g hq.ne' baseMap f hgen) y
  have hred : firstReduction q n g y = 1 := by
    apply hb
    rw [map_one]
    exact hsquare.symm.trans hfirst
  exact hy.symm.trans (top_power_of_firstReduction_one q n g hq y hred)

theorem injective (q n g : ℕ) (hq : 0 < q)
    (baseMap : TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q)
    (hb : Function.Injective baseMap)
    (f : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)))
    (hgen : ∀ i, TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (f (TorsionGenerators.CM.generator q (n + 1) g i)) =
      baseMap (TorsionGenerators.CM.generator q 1 g i)) : Function.Injective f :=
  TorsionCoordinateMaps.CM.Primary.injective_of_prime_torsion q (n + 1) f
    (TorsionCoordinateMaps.CM.Criterion.coordinates_killed q (n + 1) g)
    (first_torsion_kernel q n g hq baseMap hb f hgen)

theorem exists_coordinateEquiv (q n g : ℕ) (hq : 0 < q)
    (hdiv : Function.Surjective (fun a : A => a ^ q))
    (baseMap : TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q)
    (hb : Function.Injective baseMap)
    (hcard : Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1))) = q ^ ((n + 1) * g)) :
    ∃ e : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g ≃* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)),
      ∀ i, TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (e (TorsionGenerators.CM.generator q (n + 1) g i)) =
        baseMap (TorsionGenerators.CM.generator q 1 g i) := by
  obtain ⟨f, hf⟩ := TorsionCoordinateMaps.CM.FirstLevel.exists_lifted_coordinateMap q n g hdiv
    (fun i => baseMap (TorsionGenerators.CM.generator q 1 g i))
  exact ⟨TorsionCoordinateMaps.CM.Criterion.coordinateEquiv q (n + 1) g hq.ne' hcard f
    (first_torsion_kernel q n g hq baseMap hb f hf), hf⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoordinateReduction.CM.LiftedInjectivity

end

end OAI
