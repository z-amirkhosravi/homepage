// Sample the desktop's nonuniform channel stops at the renderer's 256 lookup
// positions. In particular, Jet's red, green and blue breakpoints differ.
function segmentedRamp(red, green, blue) {
  return Array.from({ length: 256 }, (_, i) =>
    [red, green, blue].map((stops) => {
      const x = i / 255;
      let j = 1;
      while (j < stops.length - 1 && x > stops[j][0]) j++;
      const [a, u] = stops[j - 1],
        [b, v] = stops[j];
      return u + ((v - u) * (x - a)) / (b - a);
    }),
  );
}
// Page-owned palettes; all except Teal use headers/cmap.h's color stops.
// The engine still accepts arbitrary host colors without a built-in palette.
export const colormaps = {
  Teal: ["#071b2e", "#168c9d", "#7ee0ca", "#fff0b0"],
  Jet: segmentedRamp(
    [
      [0, 0],
      [0.35, 0],
      [0.66, 1],
      [0.89, 1],
      [1, 0.5],
    ],
    [
      [0, 0],
      [0.125, 0],
      [0.375, 1],
      [0.64, 1],
      [0.91, 0],
      [1, 0],
    ],
    [
      [0, 0.5],
      [0.11, 1],
      [0.34, 1],
      [0.65, 0],
      [1, 0],
    ],
  ),
  Wistia: ["#e4ff7a", "#ffe81a", "#ffbd00", "#ffa000", "#fc7f00"],
  Hot: segmentedRamp(
    [
      [0, 0.0416],
      [0.365079, 1],
      [1, 1],
    ],
    [
      [0, 0],
      [0.365079, 0],
      [0.746032, 1],
      [1, 1],
    ],
    [
      [0, 0],
      [0.746032, 0],
      [1, 1],
    ],
  ),
  HSV: segmentedRamp(
    [
      [0, 1],
      [0.15873, 1],
      [0.174603, 0.96875],
      [0.333333, 0.03125],
      [0.349206, 0],
      [0.666667, 0],
      [0.68254, 0.03125],
      [0.84127, 0.96875],
      [0.857143, 1],
      [1, 1],
    ],
    [
      [0, 0],
      [0.15873, 0.9375],
      [0.174603, 1],
      [0.507937, 1],
      [0.666667, 0.0625],
      [0.68254, 0],
      [1, 0],
    ],
    [
      [0, 0],
      [0.333333, 0],
      [0.349206, 0.0625],
      [0.507937, 1],
      [0.84127, 1],
      [0.857143, 0.9375],
      [1, 0.09375],
    ],
  ),
  Winter: [
    [0, 0, 1],
    [0, 1, 0.5],
  ],
  CMRmap: [
    [0, 0, 0],
    [0.15, 0.15, 0.5],
    [0.3, 0.15, 0.75],
    [0.6, 0.2, 0.5],
    [1, 0.25, 0.15],
    [0.9, 0.5, 0],
    [0.9, 0.75, 0.1],
    [0.9, 0.9, 0.5],
    [1, 1, 1],
  ],
  Autumn: ["#ff0000", "#ffff00"],
  Cool: ["#00ffff", "#ff00ff"],
  Grayscale: ["#000000", "#ffffff"],
};
export const defaultColormap = "Jet";
