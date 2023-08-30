// https://www.computerenhance.com/p/efficient-dda-circle-outlines/comments
//
// Usage:
// clang -o circle-rasterizer circle-rasterizer.c && ./circle-rasterizer > circle.pbm && open circle.pbm

#include <stdio.h>

int main(void)
{
    char Bitmap[64][64] = {};

    // NOTE(casey): Center and radius of the circle
    int Cx = 32;
    int Cy = 32;
    int R = 20;

    // NOTE(casey): Loop that draws the circle
    {
        int R2 = R+R;

        int X = R;
        int Y = 0;
        int dY = -2;
        int dX = R2+R2 - 4;
        int D = R2 - 1;

        while(Y <= X)
        {
            Bitmap[Cy - Y][Cx - X] = 1;
            Bitmap[Cy - Y][Cx + X] = 1;
            Bitmap[Cy + Y][Cx - X] = 1;
            Bitmap[Cy + Y][Cx + X] = 1;
            Bitmap[Cy - X][Cx - Y] = 1;
            Bitmap[Cy - X][Cx + Y] = 1;
            Bitmap[Cy + X][Cx - Y] = 1;
            Bitmap[Cy + X][Cx + Y] = 1;

            D += dY;
            dY -= 4;
            ++Y;

#if 0
            // NOTE(casey): Branching version
            if(D < 0)
            {
                D += dX;
                dX -= 4;
                --X;
            }
#else
            // NOTE(casey): Branchless version
            int Mask = (D >> 31);
            D += dX & Mask;
            dX -= 4 & Mask;
            X += Mask;
#endif
        }
    }

    // NOTE(casey): Output the bitmap using roughly square elements
    printf("P1\n");
    printf("64 64\n");
    for(int Y = 0; Y < 64; ++Y)
    {
        for(int X = 0; X < 64; ++X)
        {
            printf("%d ", Bitmap[Y][X]);
        }
        printf("\n");
    }
}
