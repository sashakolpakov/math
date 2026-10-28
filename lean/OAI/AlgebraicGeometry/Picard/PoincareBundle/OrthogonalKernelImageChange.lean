import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Orthogonal Kernel Image Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalKernelImageChange

noncomputable section

/-! Full orthogonality is unchanged by an actual inclusion-compatible presentation of the subgroup kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

variable {S : Scheme.{u}} {H J K : Over S} [GrpObj K]
  (i : H ⟶ K) (j : J ⟶ K) (r : H ⟶ J) (h : r ≫ j = i)
  (e : ∀ T : Over S, (T ⟶ K) →* (T ⟶ K) →* Γ(T.left, ⊤)ˣ)

include h in
/-- Testing against a containing subgroup already tests against every point of the included subgroup. -/
theorem restrict {T : Over S} (y : T ⟶ K) (hy : y ∈ NaturalPairingOrthogonal.orthogonal j e T) : y ∈ NaturalPairingOrthogonal.orthogonal i e T := by
  intro U a x
  simpa only [Category.assoc, h] using hy U a (x ≫ r)

variable {A B C : Over S} [GrpObj B] [GrpObj C]
  (f : A ⟶ B) (g : A ⟶ C)
  (i' : Kernel.Scheme.kernelObject f ⟶ K) (j' : Kernel.Scheme.kernelObject g ⟶ K) (t : K ⟶ A) [Mono t]
  (r' : Kernel.Scheme.kernelObject f ⟶ Kernel.Scheme.kernelObject g)
  (hr : r' ≫ Kernel.Scheme.kernelInclusion g = Kernel.Scheme.kernelInclusion f)
  (hi : i' ≫ t = Kernel.Scheme.kernelInclusion f) (hj : j' ≫ t = Kernel.Scheme.kernelInclusion g)

include hr hi hj in
omit [GrpObj K] in
/-- Equality of the actual ambient subgroup inclusions determines the kernel-image factorization. -/
theorem factorization : r' ≫ j' = i' := by
  apply (cancel_mono t).mp
  rw [Category.assoc, hj, hr, hi]

include hr hi hj in
/-- Full scheme-valued orthogonality respects the actual ambient kernel inclusions. -/
theorem of_inclusions {T : Over S} (y : T ⟶ K) (hy : y ∈ NaturalPairingOrthogonal.orthogonal j' e T) : y ∈ NaturalPairingOrthogonal.orthogonal i' e T :=
  restrict i' j' r' (factorization f g i' j' t r' hr hi hj) e y hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalKernelImageChange
