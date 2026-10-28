import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeCompactness
import OAI.RepresentationTheory.Theta.Geometric.StableCMRealLattice

/-! # Arithmetic Compactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticCompactness.HermitianArithmetic

noncomputable section

/-! An arbitrary anisotropic Hermitian form and its original full stable
lattice give a compact quotient of the full archimedean group. The
arithmetic subgroup is the image of the literal principal lattice
subgroup intersected with the original special unitary group. -/

open scoped _root_.NumberField
open _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def integralAction (H : Matrix (Fin 3) (Fin 3) E) :
    Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) →*
      (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℤ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :=
  NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers.Construction.restrictScalarsAutomorphismHom.comp
    (Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)).subtype

def latticeStabilizer (H : Matrix (Fin 3) (Fin 3) E)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    Subgroup (Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) where
  carrier := {g | ∀ v, g.val v ∈ Λ ↔ v ∈ Λ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro g h hg hh v
    exact (hg (h.val v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    change g.val.symm v ∈ Λ ↔ v ∈ Λ
    have hv := hg (g.val.symm v)
    rw [LinearEquiv.apply_symm_apply] at hv
    exact hv.symm

variable (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

def archimedeanHom (H : Matrix (Fin 3) (Fin 3) E) :
    Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) →*
      (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).ArchimedeanProduct Set.univ :=
  ((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).diagonal Set.univ).comp
    (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H).toMonoidHom

theorem lattice_arithmeticPresentation (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation (ArithmeticModel.HermitianArithmetic.connectedGroup δ hδ hδ0 H hH hdet)
      (archimedeanHom δ hδ hδ0 H) (latticeStabilizer H Λ) := by
  exact Principal.LatticeCompactness.arithmeticPresentation_of_latticeAction_coordinates
    (ArithmeticModel.HermitianArithmetic.connectedGroup δ hδ hδ0 H hH hdet) (integralAction H) Λ.toAddSubgroup
    (latticeStabilizer H Λ) (fun _ => Iff.rfl)
    (RepresentationTheory.Theta.Geometric.StableCMRealLattice.stableRealLattice Λ hΛ δ hδ hδ0) (ArithmeticModel.HermitianArithmetic.rationalEquiv δ hδ hδ0 H)
    (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).toAddEquiv
    (ArithmeticModel.HermitianArithmetic.rationalEquiv_action δ hδ hδ0 H) (RepresentationTheory.Theta.Geometric.StableCMRealLattice.stableRealLattice_mem Λ hΛ δ hδ hδ0)

def principalArchimedeanHom (H : Matrix (Fin 3) (Fin 3) E)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ) :
    ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
      Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)) →*
        (ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).ArchimedeanProduct Set.univ :=
  (archimedeanHom δ hδ hδ0 H).comp (Subgroup.inclusion inf_le_right)

theorem principalArchimedeanHom_range (H : Matrix (Fin 3) (Fin 3) E)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ) :
    (principalArchimedeanHom δ hδ hδ0 H Λ N).range =
      ((Groups.principalLatticeSubgroup (R := ℤ) Λ.toAddSubgroup N).comap
        (integralAction H)).map (archimedeanHom δ hδ hδ0 H) := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨⟨h.val, h.property.2⟩, h.property.1, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h.val, hh, h.property⟩, rfl⟩

theorem principal_archimedean_compact (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0)
    (μ : E →+* ℂ) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : N ≠ 0) :
    CompactSpace ((ArithmeticModel.HermitianArithmetic.algebraicGroup δ hδ hδ0 H).ArchimedeanProduct Set.univ ⧸
      (principalArchimedeanHom δ hδ hδ0 H Λ N).range) := by
  let : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.1
  let : AddGroup.FG Λ.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp inferInstance
  rw [principalArchimedeanHom_range]
  exact Principal.LatticeCompactness.principalAction_arithmetic_compact (ArithmeticModel.HermitianArithmetic.connectedGroup δ hδ hδ0 H hH hdet)
    (archimedeanHom δ hδ hδ0 H) (integralAction H) Λ.toAddSubgroup
    (latticeStabilizer H Λ) (fun _ => Iff.rfl)
    (lattice_arithmeticPresentation δ hδ hδ0 H hH hdet Λ hΛ)
    (ArithmeticModel.HermitianArithmetic.connectedGroup_anisotropic δ hδ hδ0 H hH hdet han μ) N hN

theorem principal_archimedean_discrete (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : N ≠ 0) :
    DiscreteTopology (principalArchimedeanHom δ hδ hδ0 H Λ N).range := by
  let : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.1
  let : AddGroup.FG Λ.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp inferInstance
  rw [principalArchimedeanHom_range]
  exact Principal.LatticeCompactness.principalAction_arithmetic_discrete (ArithmeticModel.HermitianArithmetic.connectedGroup δ hδ hδ0 H hH hdet)
    (archimedeanHom δ hδ hδ0 H) (integralAction H) Λ.toAddSubgroup
    (latticeStabilizer H Λ) (fun _ => Iff.rfl)
    (lattice_arithmeticPresentation δ hδ hδ0 H hH hdet Λ hΛ) N hN

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArithmeticCompactness.HermitianArithmetic
