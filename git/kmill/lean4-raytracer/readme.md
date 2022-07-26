# Simple raytracer in Lean 4

[Lean 4](https://github.com/leanprover/lean4) is a dependently typed programming language, and 
it can be used both as a proof assistant and for practical programs.

This repository implements the ray tracer described in 
[_Ray Tracing in One Weekend_](https://raytracing.github.io/books/RayTracingInOneWeekend.html).
Code for writing PPM files originally came from
[TOTBWF/lean4-raytrace](https://github.com/TOTBWF/lean4-raytrace).

The raytracer uses `Task`s to render in parallel.  Part of a raytracer is using supersampling
to better estimate the amount of light entering each pixel, so it is trivial to parallelize:
the entire image is rendered multiple times, and the results are averaged together.
The following execution times are with respect to an older version of the code, and the new one is
somewhat faster, for example the first test image now takes about 8.5 minutes with the same setup.

![final test image](https://github.com/kmill/lean4-raytracer/blob/master/test13.png?raw=true)

(10 minutes with 8 threads on an Intel Xeon E5-2665. 500x333 pixels, 80 total samples per pixel, max depth 30.)

![final test image, higher resolution](https://github.com/kmill/lean4-raytracer/blob/master/test13.bigger.png?raw=true)

(2 hours with 16 threads on an Intel Xeon E5-2665. 800x533 pixels, 480 total samples per pixel, max depth 50.)

## Running the code

Assuming you already have Lean 4 setup, this builds an executable and runs it:
```
$ lake build && time ./build/bin/render test.ppm
```
The rendering settings are hard-coded in `writeTestImage` in `render.lean`.

## C benchmark

The `c` folder contains an implementation of the raytracer in C, hand translated from Lean using C idioms.
This is not meant to be a fair comparison, and I spent more time thinking about optimizing the C version.
The only purpose here is to get some idea of the relative speed of my Lean code.

The first test image in C took 20 seconds with the same configuration, and the second test image took 3 minutes 30 seconds with the same configuration.  This means my Lean program takes about 32x as long to run as the C version. (This was using the earlier version of the Lean program. The new one is about 25x.)

The current version incorporates optimizations from the [optimize-lean](https://github.com/kmill/lean4-raytracer/tree/optimize-lean) branch.
