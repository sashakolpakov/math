import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.LocalSurjectivity

/-! # Section Hom Local Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHomLocalSurjectivity.Construction

/-! Local surjectivity from actual section homomorphisms, keeping the
original type-valued presheaves and their restriction maps. -/

open _root_.CategoryTheory Opposite

universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {P Q R : Cᵒᵖ ⥤ Type w}
  [∀ T, CommGroup (P.obj T)] [∀ T, CommGroup (Q.obj T)] [∀ T, CommGroup (R.obj T)]
  (f : P ⟶ Q) (g : Q ⟶ R)
  (F : ∀ T : C, P.obj (op T) →* Q.obj (op T))
  (hF : ∀ (T : C) (x : P.obj (op T)), F T x = f.app (op T) x)
  (G : ∀ T : C, Q.obj (op T) →* R.obj (op T))
  (hG : ∀ (T : C) (x : Q.obj (op T)), G T x = g.app (op T) x)
  (ρ : ∀ {T U : C} (_a : U ⟶ T), Q.obj (op T) →* Q.obj (op U))
  (hρ : ∀ {T U : C} (a : U ⟶ T) (x : Q.obj (op T)), ρ a x = Q.map a.op x)

include F hF G hG ρ hρ in
set_option backward.isDefEq.respectTransparency false in
theorem locallySurjective_of_section_homs
    [Presheaf.IsLocallySurjective J (f ≫ g)]
    (hkernel : ∀ (T : C) (x : Q.obj (op T)), g.app (op T) x = 1 →
      Presheaf.imageSieve f x ∈ J T) : Presheaf.IsLocallySurjective J f := by
  have fmul (T : C) (x y : P.obj (op T)) :
      f.app (op T) (x * y) = f.app (op T) x * f.app (op T) y := by
    simp only [← hF, map_mul]
  have gmul (T : C) (x y : Q.obj (op T)) :
      g.app (op T) (x * y) = g.app (op T) x * g.app (op T) y := by
    simp only [← hG, map_mul]
  have ginv (T : C) (x : Q.obj (op T)) : g.app (op T) x⁻¹ = (g.app (op T) x)⁻¹ := by
    simp only [← hG, map_inv]
  constructor
  intro T y
  apply J.transitive (Presheaf.imageSieve_mem J (f ≫ g) (g.app (op T) y))
  intro U a ha
  let x : P.obj (op U) := Presheaf.localPreimage (f ≫ g) (g.app (op T) y) a ha
  have hx : g.app (op U) (f.app (op U) x) = R.map a.op (g.app (op T) y) := by
    have ht := Presheaf.app_localPreimage (f ≫ g) (g.app (op T) y) a ha
    exact ht
  let d := Q.map a.op y * (f.app (op U) x)⁻¹
  have hd : g.app (op U) d = 1 := by
    change g.app (op U) (Q.map a.op y * (f.app (op U) x)⁻¹) = 1
    rw [gmul, ginv, g.naturality_apply, hx, mul_inv_cancel]
  apply J.superset_covering _ (hkernel U d hd)
  intro V b hb
  obtain ⟨z, hz⟩ := hb
  refine ⟨z * P.map b.op x, ?_⟩
  change f.app (op V) (z * P.map b.op x) = Q.map (b ≫ a).op y
  rw [fmul, hz, f.naturality_apply, op_comp, Q.map_comp]
  change Q.map b.op d * Q.map b.op (f.app (op U) x) = Q.map b.op (Q.map a.op y)
  rw [← hρ, ← hρ, ← hρ]
  dsimp only [d]
  rw [map_mul, map_inv, inv_mul_cancel_right]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHomLocalSurjectivity.Construction
