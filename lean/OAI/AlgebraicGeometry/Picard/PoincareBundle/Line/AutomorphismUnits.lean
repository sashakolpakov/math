import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms

/-! # Automorphism Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits

noncomputable section

/-! Actual automorphisms of line bundles are unique regular units, compatibly with pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms

variable {X Y : Scheme.{u}} {M : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)

/-- The global scalar of an actual endomorphism of a line bundle. -/
def coefficient (a : M ⟶ M) : Γ(X, ⊤) := (Isogenies.NeighborCounting.LineEndomorphisms.lineEndEquiv hM).symm a

theorem coefficient_spec (a : M ⟶ M) : Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (coefficient hM a) = a :=
  (Isogenies.NeighborCounting.LineEndomorphisms.lineEndEquiv hM).apply_symm_apply a

theorem coefficient_id : coefficient hM (𝟙 M) = 1 := by
  apply Isogenies.NeighborCounting.LineEndomorphisms.scalarEnd_injective hM
  rw [coefficient_spec, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_one]

theorem coefficient_comp (a b : M ⟶ M) :
    coefficient hM (a ≫ b) = coefficient hM a * coefficient hM b := by
  apply Isogenies.NeighborCounting.LineEndomorphisms.scalarEnd_injective hM
  rw [coefficient_spec, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_mul, coefficient_spec, coefficient_spec]

/-- An automorphism has an invertible global coefficient. -/
def unitOfAut (e : M ≅ M) : Γ(X, ⊤)ˣ where
  val := coefficient hM e.hom
  inv := coefficient hM e.inv
  val_inv := by rw [← coefficient_comp, e.hom_inv_id, coefficient_id]
  inv_val := by rw [← coefficient_comp, e.inv_hom_id, coefficient_id]

theorem scalarIso_unitOfAut (e : M ≅ M) : Isogenies.NeighborCounting.ModuleScalar.scalarIso M (unitOfAut hM e) = e := by
  apply Iso.ext
  exact coefficient_spec hM e.hom

theorem unitOfAut_injective : Function.Injective (unitOfAut hM) := by
  intro e f h
  exact (scalarIso_unitOfAut hM e).symm.trans
    ((congrArg (Isogenies.NeighborCounting.ModuleScalar.scalarIso M) h).trans (scalarIso_unitOfAut hM f))

theorem unitOfAut_refl : unitOfAut hM (Iso.refl M) = 1 := by
  apply Units.ext
  exact coefficient_id hM

theorem unitOfAut_trans (e f : M ≅ M) :
    unitOfAut hM (e ≪≫ f) = unitOfAut hM e * unitOfAut hM f := by
  apply Units.ext
  exact coefficient_comp hM e.hom f.hom

theorem unitOfAut_symm (e : M ≅ M) : unitOfAut hM e.symm = (unitOfAut hM e)⁻¹ := by
  apply Units.ext
  rfl

theorem coefficient_pullback (f : Y ⟶ X) (a : M ⟶ M) :
    coefficient (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback f M hM) ((Scheme.Modules.pullback f).map a) =
      f.appTop (coefficient hM a) := by
  apply Isogenies.NeighborCounting.LineEndomorphisms.scalarEnd_injective (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback f M hM)
  rw [coefficient_spec, ← Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback, coefficient_spec]

/-- This is arbitrary scheme pullback, with no reducedness or affineness condition. -/
theorem unitOfAut_pullback (f : Y ⟶ X) (e : M ≅ M) :
    unitOfAut (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback f M hM) ((Scheme.Modules.pullback f).mapIso e) =
      Units.map f.appTop.hom (unitOfAut hM e) := by
  apply Units.ext
  exact coefficient_pullback hM f e.hom

theorem unitOfAut_conjugate {N : X.Modules} (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (s : M ≅ N) (e : M ≅ M) :
    unitOfAut hN (s.symm ≪≫ e ≪≫ s) = unitOfAut hM e := by
  apply Units.ext
  apply Isogenies.NeighborCounting.LineEndomorphisms.scalarEnd_injective hN
  change Isogenies.NeighborCounting.ModuleScalar.scalarEnd N (coefficient hN (s.inv ≫ e.hom ≫ s.hom)) =
    Isogenies.NeighborCounting.ModuleScalar.scalarEnd N (coefficient hM e.hom)
  rw [coefficient_spec]
  calc
    s.inv ≫ e.hom ≫ s.hom = s.inv ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (coefficient hM e.hom) ≫ s.hom :=
      congrArg (fun a => s.inv ≫ a ≫ s.hom) (coefficient_spec hM e.hom).symm
    _ = Isogenies.NeighborCounting.ModuleScalar.scalarEnd N (coefficient hM e.hom) := by
      rw [Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits
