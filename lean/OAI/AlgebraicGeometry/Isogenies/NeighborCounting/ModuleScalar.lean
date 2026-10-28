import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections

/-! # Module Scalar -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

noncomputable section

/-! Scalar endomorphisms of module sheaves and arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction

variable {X Y : Scheme.{u}}

/-- Multiplication by a global regular function on an arbitrary module sheaf. -/
def scalarEnd (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val := PresheafOfModules.homMk
    { app := fun U ↦ M.smul (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)
      naturality := by
        intro U V f
        have hm := Scheme.Modules.map_comp_smul (M := M) f.unop
          (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)
        have h := congrArg (fun a ↦ a r)
          ((X.presheaf.map_comp (homOfLE (show U.unop ≤ ⊤ from le_top)).op f).symm)
        exact (congrArg (fun a ↦ M.presheaf.map f ≫ M.smul a) h).symm.trans hm.symm }
    (by
      rintro ⟨U⟩ a m
      exact smul_comm (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r)
        (show Γ(X, U) from a) (show Γ(M, U) from m))

@[simp]
theorem scalarEnd_apply (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (m : Γ(M, U)) :
    (scalarEnd M r).app U m =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • m := rfl

@[simp]
theorem scalarEnd_one (M : X.Modules) : scalarEnd M 1 = 𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  simp

theorem scalarEnd_mul (M : X.Modules) (r s : Γ(X, ⊤)) :
    scalarEnd M (r * s) = scalarEnd M r ≫ scalarEnd M s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  let j := (homOfLE (show U ≤ ⊤ from le_top)).op
  change X.presheaf.map j (r * s) • m =
    X.presheaf.map j s • (X.presheaf.map j r • m)
  rw [map_mul, mul_smul, smul_comm]

theorem scalarEnd_naturality {M N : X.Modules} (q : M ⟶ N) (r : Γ(X, ⊤)) :
    scalarEnd M r ≫ q = q ≫ scalarEnd N r := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  exact q.app_smul _ m

/-- A unit function acts by an actual sheaf isomorphism. -/
def scalarIso (M : X.Modules) (r : Γ(X, ⊤)ˣ) : M ≅ M where
  hom := scalarEnd M r
  inv := scalarEnd M ↑r⁻¹
  hom_inv_id := by rw [← scalarEnd_mul, Units.mul_inv, scalarEnd_one]
  inv_hom_id := by rw [← scalarEnd_mul, Units.inv_mul, scalarEnd_one]

theorem scalarEnd_pushforward (f : X ⟶ Y) (M : X.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pushforward f).map (scalarEnd M (f.appTop r)) =
      scalarEnd ((Scheme.Modules.pushforward f).obj M) r := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  let m' : Γ(M, f ⁻¹ᵁ U) := m
  change X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (f.appTop r) • m' =
    f.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • m'
  exact congrArg (fun a : Γ(X, f ⁻¹ᵁ U) ↦ a • m')
    (congrArg (fun q ↦ q r) (f.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op)).symm

/-- Scalar corrections commute with arbitrary scheme pullback, including
the possibly nonreduced overlap schemes of an fppf cover. -/
theorem scalarEnd_pullback (f : X ⟶ Y) (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (scalarEnd M r) =
      scalarEnd ((Scheme.Modules.pullback f).obj M) (f.appTop r) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  calc
    adj.homEquiv _ _ ((Scheme.Modules.pullback f).map (scalarEnd M r)) =
        scalarEnd M r ≫ adj.unit.app M := by
      rw [Adjunction.homEquiv_unit]
      exact (adj.unit.naturality (scalarEnd M r)).symm
    _ = adj.unit.app M ≫ scalarEnd
        ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M)) r :=
      scalarEnd_naturality (adj.unit.app M) r
    _ = adj.homEquiv _ _ (scalarEnd ((Scheme.Modules.pullback f).obj M) (f.appTop r)) := by
      rw [Adjunction.homEquiv_unit, scalarEnd_pushforward]

theorem scalarEnd_structure (q : End (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)) :
    scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X q) = q := by
  apply (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X).injective
  change X.presheaf.map (𝟙 (.op ⊤)) (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X q) * 1 = _
  simp

/-- The global unit function of a structure-sheaf automorphism. -/
def structureAutUnit (e : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) : Γ(X, ⊤)ˣ :=
  Units.map (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X).toMonoidHom
    ((Aut.unitsEndEquivAut (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).symm e)

theorem scalarEnd_structureAut (e : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) ↑(structureAutUnit e) = e.hom :=
  scalarEnd_structure e.hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar
