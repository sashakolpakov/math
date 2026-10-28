import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Regular Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: effective divisors of nonzero regular functions

On an integral Noetherian scheme, the principal divisor of a nonzero
global section has nonnegative coefficients. At a codimension-one point
its coefficient is the finite length of the local quotient by that section.
These are the multiplicities needed in specialization along t = 0.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

instance integralTopNonempty : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩

/-- Regard a global regular function as an element of the actual function field. -/
def globalFunctionFieldElement (a : Γ(X, ⊤)) : X.functionField :=
  X.germToFunctionField ⊤ a

omit [AlgebraicGeometry.IsNoetherian X] in
theorem globalFunctionFieldElement_ne_zero (a : Γ(X, ⊤)) (ha : a ≠ 0) :
    globalFunctionFieldElement X a ≠ 0 :=
  (map_ne_zero_iff _ (X.germToFunctionField_injective ⊤)).mpr ha

/-- The actual finite principal divisor of a global regular function. -/
def regularFunctionDivisor (a : Γ(X, ⊤)) : X →₀ ℤ :=
  Ord.BundleCycles.principalDivisor X (globalFunctionFieldElement X a)

/-- At codimension one, a nonzero regular function has its local quotient
length as multiplicity. Finiteness of the length is proved from Noetherianity
and the local dimension bound. -/
theorem regularFunctionDivisor_coeff_length (a : Γ(X, ⊤)) (ha : a ≠ 0)
    (x : X) (hx : coheight x = 1) :
    regularFunctionDivisor X a x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ ⊤ x (by trivial) a})).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : X.presheaf.germ ⊤ x (by trivial) a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x (by trivial))).mpr ha
  change X.ord (X.germToFunctionField ⊤ a) x = _
  apply (Scheme.ord_eq_iff hx (globalFunctionFieldElement_ne_zero X a ha)).mpr
  change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField ⊤ a) = _
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) (by trivial) a,
    Ring.ordFrac_eq_ord (X.presheaf.stalk x) hg]
  apply Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  exact (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hg))).symm

theorem regularFunctionDivisor_nonnegative (a : Γ(X, ⊤)) (ha : a ≠ 0) (x : X) :
    0 ≤ regularFunctionDivisor X a x := by
  by_cases hx : coheight x = 1
  · rw [regularFunctionDivisor_coeff_length X a ha x hx]
    exact Int.natCast_nonneg _
  · change 0 ≤ X.ord (globalFunctionFieldElement X a) x
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- The divisor has no coefficient where the section is a local unit. -/
theorem regularFunctionDivisor_eq_zero_of_isUnit_germ (a : Γ(X, ⊤)) (x : X)
    (ha : IsUnit (X.presheaf.germ ⊤ x (by trivial) a)) : regularFunctionDivisor X a x = 0 := by
  by_cases hx : coheight x = 1
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change X.ord (X.germToFunctionField ⊤ a) x = 0
    have hfield : X.germToFunctionField ⊤ a ≠ 0 := by
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) (by trivial) a]
      exact (ha.map (algebraMap _ X.functionField)).ne_zero
    apply (Scheme.ord_eq_iff hx hfield).mpr
    change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField ⊤ a) = 1
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) (by trivial) a]
    exact Ring.ordFrac_of_isUnit ha
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

theorem regularFunctionDivisor_support_subset (a : Γ(X, ⊤)) :
    ((regularFunctionDivisor X a).support : Set X) ⊆ (X.basicOpen a : Set X)ᶜ := by
  classical
  intro x hx hxa
  apply (Finsupp.mem_support_iff.mp hx)
  apply regularFunctionDivisor_eq_zero_of_isUnit_germ
  exact (Scheme.mem_basicOpen X a x (by trivial)).mp hxa

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor.BundleCycles
