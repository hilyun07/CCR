#include <stdio.h>
#include <arpa/inet.h>
#include <unistd.h>

int main() 
{  
    int sockfd_client = socket(AF_INET, SOCK_STREAM, 0); 
    if (sockfd_client == -1)
    {
        puts("socket creation failed");
        return 0;
    }

    struct sockaddr_in client;    
    client.sin_family = AF_INET;  
    client.sin_addr.s_addr = inet_addr("127.0.0.1");  
    client.sin_port = htons(7000);  

    if (connect(sockfd_client, (struct sockaddr*)&client, sizeof(client)) != 0)
    {
        puts("connection failed");
        return 0;
    }

    char *buf = "ABCD";
    char *ptr_buf;
    int k, len;

    while(1) 
    {
        len = 4;
        ptr_buf = buf;

        while (len > 0)
        {
            k = send(sockfd_client, ptr_buf, len, 0);      
            if (k == -1)
            {
                puts("sending failed");
                break;
            }

            ptr_buf += k;
            len -= k;
        }
        puts("message sent");
        break;
    }  

    close(sockfd_client);  
    puts("client disconnected");

    return 0;  
}
