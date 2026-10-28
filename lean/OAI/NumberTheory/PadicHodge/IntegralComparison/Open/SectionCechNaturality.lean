import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSquare
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.QuasiIso

/-! # Section Cech Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechNaturality

noncomputable section

/-! A genuine global-to-open restriction is natural on Čech totals.
The injective open Čech edge detects quasi-isomorphisms of the original
global-section maps without any acyclicity assertion for the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type a} [Category.{b} B] [Abelian B]
  [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (G : A ⥤ Cᵒᵖ ⥤ B) [G.Additive]
  (r : F ⋙ Functor.const Cᵒᵖ ⟶ G)
  {ι : Type} [Finite ι] (U : ι → C)

local notation "D" => HomologicalComplex.complexOfFunctorsToFunctorToComplex

def global (K : CochainComplex A ℕ) := (F.mapHomologicalComplex (.up ℕ)).obj K

def diagram (K : CochainComplex A ℕ) :=
  (D).obj ((G.mapHomologicalComplex (.up ℕ)).obj K)

def cone (K : CochainComplex A ℕ) :
    (Functor.const Cᵒᵖ).obj (global F K) ⟶ diagram G K :=
  (D).map ((r.mapHomologicalComplex (.up ℕ)).app K)

def edge (K : CochainComplex A ℕ) :=
  GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (diagram G K) (global F K) (cone F G r K)

def map {K L : CochainComplex A ℕ} (f : K ⟶ L) :
    GeometricComparison.CechCone.Total.CechConeTotal.total U (diagram G K) ⟶ GeometricComparison.CechCone.Total.CechConeTotal.total U (diagram G L) :=
  (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
    ((D).map ((G.mapHomologicalComplex (.up ℕ)).map f))

variable {K L : CochainComplex A ℕ} (f : K ⟶ L)

omit [HasBinaryProducts C] [HasProducts.{0} B] [HasCoproducts.{0} B] in
theorem cone_natural : cone F G r K ≫
    (D).map ((G.mapHomologicalComplex (.up ℕ)).map f) =
      (Functor.const Cᵒᵖ).map ((F.mapHomologicalComplex (.up ℕ)).map f) ≫
        cone F G r L := by
  exact (congrArg (D).map ((r.mapHomologicalComplex (.up ℕ)).naturality f).symm).trans
    (by rw [Functor.map_comp]; rfl)

omit [Finite ι] in
theorem natural : edge F G r U K ≫ SectionCechNaturality.map G U f =
    (F.mapHomologicalComplex (.up ℕ)).map f ≫ edge F G r U L :=
  GeometricComparison.CechCone.TotalSquare.CechConeTotalConeSquare.natural U (cone F G r K) (cone F G r L)
    ((D).map ((G.mapHomologicalComplex (.up ℕ)).map f))
    ((F.mapHomologicalComplex (.up ℕ)).map f) (cone_natural F G r f)

variable {M : CochainComplex B ℕ} (s : M ⟶ global F K)
  (hsource : QuasiIso (s ≫ edge F G r U K))
  (hmap : QuasiIso (SectionCechNaturality.map G U f)) (hedge : QuasiIso (edge F G r U L))

include hsource hmap hedge in
omit [Finite ι] in
theorem quasiIso : QuasiIso (s ≫ (F.mapHomologicalComplex (.up ℕ)).map f) := by
  let := hsource
  let := hmap
  let := hedge
  apply (quasiIso_iff_comp_right _ (edge F G r U L)).mp
  have h : (s ≫ edge F G r U K) ≫ SectionCechNaturality.map G U f =
      (s ≫ (F.mapHomologicalComplex (.up ℕ)).map f) ≫ edge F G r U L := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => s ≫ t) (natural F G r U f)).trans
        (Category.assoc _ _ _).symm)
  exact h ▸ inferInstanceAs (QuasiIso ((s ≫ edge F G r U K) ≫ SectionCechNaturality.map G U f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechNaturality
