import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineHomDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CharacterSpan

/-! # Line Character Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterDetection

noncomputable section

/-!
# CartierDuality: kernel characters distinguish pullback-trivialized line bundles
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace Construction.LineDescent

/-- An isomorphism intertwines two maps in both directions. -/
theorem inverse_intertwines {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ : C} (e : A₁ ≅ B₁) (d : A₂ ≅ B₂)
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (h : e.hom ≫ b = a ≫ d.hom) :
    e.inv ≫ a = b ≫ d.inv := by
  apply (cancel_epi e.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Compatible actual line-bundle isomorphisms descend through the cover. -/
theorem nonempty_iso_of_compatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ (Scheme.Modules.pullback f).obj M.sheaf)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map e.hom ≫ (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf).hom q x y hx hy =
        (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf).hom q x y hx hy ≫ (Scheme.Modules.pullback y).map e.hom) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let b := Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentHom f e.hom he
  let c := Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentHom f e.inv (fun q x y hx hy =>
    inverse_intertwines ((Scheme.Modules.pullback x).mapIso e) ((Scheme.Modules.pullback y).mapIso e)
      ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf).hom q x y hx hy)
      ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf).hom q x y hx hy) (he q x y hx hy))
  obtain ⟨a, ha, _⟩ := LineHomDescent.Construction.LineDescent.existsUnique_lineHom_descent f L M b
  obtain ⟨d, hd, _⟩ := LineHomDescent.Construction.LineDescent.existsUnique_lineHom_descent f M L c
  have ha' : (Scheme.Modules.pullback f).map a = e.hom := ha
  have hd' : (Scheme.Modules.pullback f).map d = e.inv := hd
  refine ⟨⟨a, d, ?_, ?_⟩⟩
  · apply LineHomDescent.Construction.LineDescent.pullbackHom_injective_lines f L L
    rw [Functor.map_comp, ha', hd', e.hom_inv_id, CategoryTheory.Functor.map_id]
  · apply LineHomDescent.Construction.LineDescent.pullbackHom_injective_lines f M M
    rw [Functor.map_comp, hd', ha', e.inv_hom_id, CategoryTheory.Functor.map_id]

end Construction.LineDescent

namespace Construction.KernelCharacters

open scoped _root_.CategoryTheory.MonObj

/-- Every class in the pullback kernel has an actual representative
and an actual trivialization, obtained from equality of module-sheaf classes. -/
theorem exists_trivialized_representative
    {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (q : {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left}) :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = q.val ∧
      Nonempty ((Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep q.val
  refine ⟨L, hL, ?_⟩
  exact Quotient.exact ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left) hL).trans q.property)

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable [IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left]
variable [Flat f.left] [Surjective f.left] [QuasiCompact f.left]

/-- Equal characters give isomorphic original line bundles; the proof
uses the complete native gluing relation, including nonreduced tests. -/
theorem line_iso_of_character_eq
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (d : (Scheme.Modules.pullback f.left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (.op R)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i.hom]
    (h : Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter L e R i.hom = Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter M d R i.hom) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have hs := Picard.Homomorphisms.LineKernelCharacters.Construction.kernelCocycleCoordinateCharacter_eq_implies_scalar_eq
    (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e) (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f M d) R i h
  exact LineDescent.nonempty_iso_of_compatible f.left L M (e ≪≫ d.symm)
    (fun q x y hx hy => Picard.Homomorphisms.KernelCharacterDetection.Construction.kernelScalar_eq_implies_native_compatible
      (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f L) (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f M) e d hs q x y hx hy)

/-- The pullback kernel of actual line-bundle classes embeds into the
coordinate characters of the scheme-theoretic kernel. -/
def pullbackKernelCharacterEmbedding
    (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (.op R)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i.hom] :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} ↪ GroupLike k R := by
  choose L hL e using exists_trivialized_representative f
  refine ⟨fun q => Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter (L q) (Classical.choice (e q)) R i.hom, ?_⟩
  intro q r h
  apply Subtype.ext
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L r) :=
    Quotient.sound (line_iso_of_character_eq f (L q) (L r)
      (Classical.choice (e q)) (Classical.choice (e r)) R i h)
  exact (hL q).symm.trans (he.trans (hL r))

/-- A finite-dimensional kernel Hopf algebra permits only finitely
many line-bundle classes trivialized by the group morphism. -/
theorem finite_pullbackKernel
    (R : CommHopfAlgCat k) [Module.Finite k R]
    (i : ((hopfSpec (.of k)).obj (.op R)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i.hom] :
    Finite {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} := by
  have : Finite (GroupLike k R) := Picard.Homomorphisms.CharacterSpan.Construction.finite_coordinateCharacters k R
  exact Finite.of_injective _ (pullbackKernelCharacterEmbedding f R i).injective

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterDetection
