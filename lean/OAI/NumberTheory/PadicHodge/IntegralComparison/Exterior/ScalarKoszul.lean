import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.KoszulCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.PowerVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveConeExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.RegularSequenceKoszul

/-! # Scalar Koszul -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ScalarKoszul.Comparison

noncomputable section

/-! The actual exterior Koszul complex, extended to nonpositive degrees,
is isomorphic to the previously constructed scalar-cone Koszul complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix OAI.NumberTheory.PadicHodge.IntegralComparison.RegularElementKoszul

universe u
variable (R : Type u) [CommRing R]

abbrev shape := NonpositiveProjectiveResolution.shape

abbrev exterior {n : ℕ} (s : Fin n → R) :=
  KoszulComplex.complex R (Fin n → R) (Koszul.GeneratorMatrix.equation R s)

abbrev extended {n : ℕ} (s : Fin n → R) := (exterior R s).extend shape

theorem extend_scalar (K : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    extendMap (r • 𝟙 K) shape = RegularElementKoszul.scalar (K.extend shape) r := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : ∃ n, shape.f n = i
  · obtain ⟨n, hn⟩ := hi
    rw [extendMap_f _ shape hn]
    change (K.extendXIso shape hn).hom ≫ (r • 𝟙 (K.X n)) ≫
      (K.extendXIso shape hn).inv = r • 𝟙 _
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.hom_inv_id]
  · exact (K.isZero_extend_X shape i (fun n hn => hi ⟨n, hn⟩)).eq_of_src _ _

def scalarConeIso {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : K ≅ L) (r : R) :
    CochainComplex.mappingCone (RegularElementKoszul.scalar K r) ≅ CochainComplex.mappingCone (RegularElementKoszul.scalar L r) :=
  homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
    (Arrow.isoMk e e (RegularElementKoszul.scalar_naturality e.hom r).symm)

theorem empty_isZero (s : Fin 0 → R) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((extended R s).X i) := by
  by_cases him : ∃ n, shape.f n = i
  · obtain ⟨n, hn⟩ := him
    have hp : 0 < n := by
      by_contra h
      have hn0 : n = 0 := by omega
      subst n
      apply hi
      simpa [shape, NonpositiveProjectiveResolution.shape] using hn.symm
    let : Subsingleton ((exterior R s).X n) :=
      PowerVanishing.subsingleton (Pi.basisFun R (Fin 0)) hp
    exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
      ((exterior R s).extendXIso shape hn)
  · exact (exterior R s).isZero_extend_X shape i (fun n hn => him ⟨n, hn⟩)

def emptyTermIso (s : Fin 0 → R) (i : ℤ) :
    (extended R s).X i ≅ (RegularElementKoszul.single.obj (ModuleCat.of R R)).X i := by
  by_cases hi : i = 0
  · subst i
    exact (exterior R s).extendXIso shape (i := 0) (by simp [shape]) ≪≫
      (exteriorPower.zeroEquiv R (Fin 0 → R)).toModuleIso ≪≫
        (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).symm
  · exact (empty_isZero R s i hi).iso (isZero_single_obj_X (.up ℤ) 0 _ i hi)

def emptyIso (s : Fin 0 → R) : extended R s ≅ RegularElementKoszul.single.obj (ModuleCat.of R R) :=
  Hom.isoOfComponents (emptyTermIso R s) (by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by change 0 + 1 = j at hij; omega
      exact (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj).eq_of_tgt _ _
    · exact (empty_isZero R s i hi).eq_of_src _ _)

def stepIso {n : ℕ} (s : Fin (n + 1) → R) :
    extended R s ≅ CochainComplex.mappingCone
      (RegularElementKoszul.scalar (extended R (s ∘ Fin.castSucc)) (s (Fin.last n))) :=
  (shape.extendFunctor (ModuleCat R)).mapIso (Finite.KoszulCone.iso R n s).symm ≪≫
    NonpositiveConeExtension.iso _ ≪≫
      eqToIso (congrArg
        (fun a : extended R (s ∘ Fin.castSucc) ⟶ extended R (s ∘ Fin.castSucc) =>
          CochainComplex.mappingCone a)
        (extend_scalar R (exterior R (s ∘ Fin.castSucc)) (s (Fin.last n))))

theorem exists_iso (n : ℕ) (s : Fin n → R) :
    Nonempty (extended R s ≅ RegularSequenceKoszul.complex (ModuleCat.of R R) (List.ofFn s)) := by
  induction n with
  | zero => exact ⟨emptyIso R s⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih (s ∘ Fin.castSucc)
    refine ⟨stepIso R s ≪≫ scalarConeIso R e (s (Fin.last n)) ≪≫ eqToIso ?_⟩
    rw [List.ofFn_succ', List.concat_eq_append, RegularSequenceKoszul.complex_append_singleton]
    rfl

def iso {n : ℕ} (s : Fin n → R) :
    extended R s ≅ RegularSequenceKoszul.complex (ModuleCat.of R R) (List.ofFn s) :=
  Classical.choice (exists_iso R n s)

theorem exists_augmentation {n : ℕ} (s : Fin n → R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s)) :
    ∃ ε : extended R s ⟶ RegularElementKoszul.single.obj
      (RegularSequenceKoszul.quotient (ModuleCat.of R R) (List.ofFn s)), QuasiIso ε := by
  obtain ⟨ε, hε⟩ := RegularSequenceKoszul.exists_augmentation (ModuleCat.of R R) (List.ofFn s) hs
  let := hε
  exact ⟨(Comparison.iso R s).hom ≫ ε, quasiIso_comp _ _⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ScalarKoszul.Comparison
