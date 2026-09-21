# The demo programs

Four short programs, one per mechanism, each written so that the same
thing in C needs either a test the programmer has to remember or a
round with the verifier. They are held to everything the rest of the
corpus is held to, at every stage, so a change to the language that
breaks one of them fails the run.

| program | the mechanism | what to look at |
| --- | --- | --- |
| `parse.ko` | places with typed extents | one `?` per header, and every field of the view free afterwards |
| `bounds.ko` | refinement types | the bound declared on the map's value, and the index that needs no test |
| `lock.ko` | scoped resources | the `drop` inside the lock block, which unlocks on the way out |
| `resize.ko` | guards | the view that dies at the resize, and the diagnostic that names the line |

Each comment claims something about what the checker does. All of them
are true of the checker as it stands; the way to see one is to break
the line the comment is about and read what comes back:

    koitc check tests/demo/parse.ko

Take the `?` off the marked load in `bounds.ko` and the index stops
being in range. Move `ktime()` inside the lock block in `lock.ko` and
the call effect is refused, with the `hold` line named. Read
`eth.proto` after the resize in `resize.ko` and the view is gone, with
the line that dropped it named. Drop the `hton` around the constant in
`parse.ko` and the byte-order comparison does not type.
