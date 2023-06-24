# The notations used by this library

- Categories are denoted $\mathcal{C, D,}\ldots$, which can be written `\McC, \McD, ...`
  - Objects should be capital letters, starting at either `A`, `P`, or `X`, and avoid collisions with functors.
  - Arrows should be lowercase letters, starting at `f`.
- Functors are denoted by capital letters, starting at `F`.
  - A functor from $\mathcal{C}$ to $\mathcal{D}$ is $\mathcal{C} \Rightarrow \mathcal{D}$, the arrow can be written in lean with `\Right`.
  - Functor composition is $\cdot$, can be written `\bu`.
- Natural transformations are lowercase Greek letters.
  - A natural transformation from `F` to `G` is $F \gg G$, which can be written with `\gg`.
  - The composition is $\circledcirc$, written with `\oo`.
