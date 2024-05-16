# 《The essence of ML type inference》的中文翻译和阅读笔记

# Chinese Translation and Comments for "The essence of ML type inference"

["The Essence of ML type inference"](http://cristal.inria.fr/attapl/) is a chapter of ["Advanced Topics in Types and Programming Languages"](https://www.cis.upenn.edu/~bcpierce/attapl/index.html). 


[《The essence of ML type inference》](http://cristal.inria.fr/attapl/)是[《Advanced Topics in Types and Programming Languages》](https://www.cis.upenn.edu/~bcpierce/attapl/index.html)的一个章节。

- 基于[这里](http://cristal.inria.fr/attapl/)的拓展版本进行翻译。

翻译流程：

1. 使用 MathPix 会员识别pdf文件为markdown。识别结果在[mathpix](mathpix/)文件夹
2. 使用 智谱 GLM4 API 进行逐段翻译。脚本为`translation.py`
   - 生成了纯翻译结果`translated.md`以及中英混合的`translated_mix.md`
3. 使用fix_url.py将markdown的图片下载到本地。生成`translated_mix_fixurl.md`
4. （未完全完成） 人工校对，使用GPT4等大模型辅助理解，并记录下相应的笔记。

目前校对并增加了笔记的章节：

- 1.2节：1.2.12 开始的后半部分 
- 1.3节：到1.3.9左右
