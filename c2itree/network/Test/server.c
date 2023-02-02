#include <stdio.h>
#include <arpa/inet.h>
#include <unistd.h>

int main() 
{
    int sockfd_server = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd_server == -1)
    {
        puts("socket creation failed");
        return 0;
    }

    struct sockaddr_in server;
    server.sin_family = AF_INET;
    server.sin_addr.s_addr = inet_addr("0.0.0.0");
    server.sin_port = htons(7000);
    if (bind(sockfd_server, (struct sockaddr*)&server, sizeof(server)) != 0)
    {
        puts("socket binding failed");
        return 0;
    }

    if (listen(sockfd_server, 1) != 0)
    {
        puts("listening failed");
        return 0;
    }

    struct sockaddr_in client;
    socklen_t len = sizeof(client);
    int sockfd_client = accept(sockfd_server, (struct sockaddr*)&client, &len);
    if (sockfd_client == -1)
    {
        puts("accepting failed");
        return 0;
    }

    char buf[100];
    int k;

    while(1)
    {
        k = recv(sockfd_client, buf, 100, 0);
        if (k == -1)
        {
            puts("receiving failed");
            break;
        }

        if (k == 0)
        {
            puts("client disconnected");
            break;
        }

        if (k > 0)
        {
            puts("message received");
            puts(buf);
            break;
        }
    }

    close(sockfd_client);
    close(sockfd_server);

    puts("connection ended");
    return 0;
}
